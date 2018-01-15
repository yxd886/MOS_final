#define _LARGEFILE64_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdint.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <dirent.h>
#include <string.h>
#include <time.h>
#include <pthread.h>
#include <signal.h>
#include <linux/if_ether.h>
#include <linux/tcp.h>
#include <mos_api.h>
#include <ctype.h>
#include "cpu.h"
#include "http_parsing.h"
#include "debug.h"
#include "applib.h"
#include "aho-corasick/fpp.h"
#include "aho-corasick/aho.h"
#define MAX_MATCH 8192
#define false 0
#define true 1

/*----------------------------------------------------------------------------*/
/* default configuration file path */
#define MOS_CONFIG_FILE          "config/mos.conf"
/* max length per line in firewall config file */
#define CONF_MAX_LINE_LEN        1024
/* number of array elements */
#define NELEMS(x)           (sizeof(x) / sizeof(x[0])) 
/* macro to skip spaces */
#define SKIP_SPACES(x) while (*x && isspace((int)*x)) x++;
/* macro to skip characters */
#define SKIP_CHAR(x) while((*x) && !isspace(*x)) x++;
/* macro to skip digit characters */
#define SKIP_DIGIT(x) while((*x) && isdigit(*x)) x++;
/* macro to do netmasking with ip address */
#define IP_NETMASK(x, y) x & (0xFFFFFFFF >> (32 - y));
/* macro to dump error and exit */
#define EXIT_WITH_ERROR(f, m...) {                                 \
        fprintf(stderr, "[%10s:%4d] errno: %u" f, __FUNCTION__, __LINE__, errno, ##m); \
    exit(EXIT_FAILURE);                                            \
}
/* boolean for function return value */
#define SUCCESS 1
#define FAILURE 0
/*----------------------------------------------------------------------------*/
/* firewall rule action */
typedef enum {FRA_INVALID, FRA_ACCEPT, FRA_DROP} FRAction;
#define FR_ACCEPT "ACCEPT"
#define FR_DROP   "DROP"
#define FR_SPORT  "sport:"
#define FR_DPORT  "dport:"
/* firewall rule structure */
#define MAX_RULES 1024
#define MAX_IP_ADDR_LEN 19      /* in CIDR format */
/* all fields are in network byte order */
typedef struct FirewallRule {
    in_addr_t fr_srcIP;         /* source IP */
    int       fr_srcIPmask;     /* source IP netmask */
    in_addr_t fr_dstIP;         /* destination IP */
    int       fr_dstIPmask;     /* destination IP netmask */
    in_port_t fr_srcPort;       /* source port */
    in_port_t fr_dstPort;       /* destination port */
    FRAction  fr_action;        /* action */
    uint32_t  fr_count;         /* packet count */
} FirewallRule;
static FirewallRule g_FWRules[MAX_RULES];
/*----------------------------------------------------------------------------*/
struct thread_context
{
    mctx_t mctx;         /* per-thread mos context */
    int mon_listener;    /* listening socket for flow monitoring */
};
/*----------------------------------------------------------------------------*/
/* Print the entire firewall rule and status table */



/*----------------------------------------------------------------------------*/
static inline char*
ExtractPort(char* buf, in_port_t* sport, in_port_t* dport)
{
    in_port_t* p = NULL;
    char* temp = (char*)buf;
    char* check;
    int port;
    char s = 0;             /* swap character */

    SKIP_CHAR(temp);        /* skip characters */
    s = *temp; *temp = 0;   /* replace the end character with null */

    /* check if the port format is correct */
    if (!strncmp(buf, FR_SPORT, sizeof(FR_SPORT) - 1)) {
        p = sport;
        buf += (sizeof(FR_SPORT) - 1);
    }
    else if (!strncmp(buf, FR_DPORT, sizeof(FR_DPORT) - 1)) {
        p = dport;
        buf += (sizeof(FR_DPORT) - 1);
    }
    else
        EXIT_WITH_ERROR("Invalid rule in port setup [%s]\n", buf);

    check = buf;
    SKIP_DIGIT(check);
    if (check != temp)
        EXIT_WITH_ERROR("Invalid port format [%s]\n", buf);

    /* convert to port number */
    port = atoi(buf);
    if (port < 0 || port > 65536)
        EXIT_WITH_ERROR("Invalid port [%d]\n", port);
    (*p) = htons(port);

    (*temp) = s;    /* recover the original character */
    buf = temp;     /* move buf pointer to next string */
    SKIP_SPACES(buf);

    return buf;
}
/*----------------------------------------------------------------------------*/
static inline char*
ExtractIPAddress(char* buf, in_addr_t* addr, int* addrmask)
{
    struct in_addr addr_conv;
    char* temp = (char*)buf;
    char* check;
    int netmask = 32;
    char s = 0;        /* swap character */

    /* skip characters which are not '/' */
    while ((*temp) && !isspace(*temp) && (*temp) != '/') temp++;

    s = *temp; *temp = 0;
    if (inet_aton(buf, &addr_conv) == 0)
        EXIT_WITH_ERROR("Invalid IP address [%s]\n", buf);
    (*addr) = addr_conv.s_addr;
    (*temp) = s;

    /* if the rule contains netmask */
    if ((*temp) == '/') {
        buf = temp + 1;
        SKIP_CHAR(temp);
        s = *temp; *temp = 0;

        /* check if the format is correct */
        check = buf;
        SKIP_DIGIT(check);
        if (check != temp)
            EXIT_WITH_ERROR("Invalid netmask format [%s]\n", buf);

        /* convert to netmask number */
        netmask = atoi(buf);
        if (netmask < 0 || netmask > 32)
            EXIT_WITH_ERROR("Invalid netmask [%s]\n", buf);
        (*addr) = IP_NETMASK((*addr), netmask);
        (*temp) = s;
    }

    /* move buf pointer to next string */
    buf = temp;
    SKIP_SPACES(buf);

    (*addrmask) = netmask;

    return buf;
}
/*----------------------------------------------------------------------------*/
static void
ParseConfigFile(char* configF)
{
    FirewallRule *fwr;
    FILE *fp;
    char line_buf[CONF_MAX_LINE_LEN] = {0};
    char *line, *p;
    int i = 0;

    /* config file path should not be null */
    assert(configF != NULL);

    /* open firewall rule file */
    if ((fp = fopen(configF, "r")) == NULL)
        EXIT_WITH_ERROR("Firewall rule file %s is not found.\n", configF);

    /* read each line */
    while ((line = fgets(line_buf, CONF_MAX_LINE_LEN, fp)) != NULL) {

        /* each line represents a rule */
        fwr = &g_FWRules[i];
        if (line[CONF_MAX_LINE_LEN - 1])
            EXIT_WITH_ERROR("%s has a line longer than %d\n",
                        configF, CONF_MAX_LINE_LEN);

        SKIP_SPACES(line); /* remove spaces */
        if (*line == '\0' || *line == '#')
            continue;
        if ((p = strchr(line, '#'))) /* skip comments in the line */
            *p = '\0';
        while (isspace(line[strlen(line) - 1])) /* remove spaces */
            line[strlen(line) - 1] = '\0';

        /* read firewall rule action */
        p = line;
        if (!strncmp(p, FR_ACCEPT, sizeof(FR_ACCEPT) - 1)) {
            fwr->fr_action = FRA_ACCEPT;
            p += (sizeof(FR_ACCEPT) - 1);
        }
        else if (!strncmp(p, FR_DROP, sizeof(FR_DROP) - 1)) {
            fwr->fr_action = FRA_DROP;
            p += (sizeof(FR_DROP) - 1);
        }
        else
            EXIT_WITH_ERROR("Unknown rule action [%s].\n", line);

        if (!isspace(*p)) /* invalid if no space exists after action */
            EXIT_WITH_ERROR("Invalid format [%s].\n", line);
        SKIP_SPACES(p);

        /* read client ip address */
        if (*p)
            p = ExtractIPAddress(p, &fwr->fr_srcIP, &(fwr->fr_srcIPmask));
        else
            EXIT_WITH_ERROR("Invalid format [%s].\n", line);

        /* read server ip address */
        if (*p)
            p = ExtractIPAddress(p, &fwr->fr_dstIP, &(fwr->fr_dstIPmask));
        else
            EXIT_WITH_ERROR("Invalid format [%s].\n", line);

        /* read port filter information */
        while (*p)
            p = ExtractPort(p, &(fwr->fr_srcPort), &(fwr->fr_dstPort));

        fwr->fr_count = 0;
        if ((i++) >= MAX_RULES)
            EXIT_WITH_ERROR("Exceeded max number of rules (%d)\n", MAX_RULES);
    }

    fclose(fp);
}
/*----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------*/

struct ids_flow_state{
    uint32_t _state;
    uint32_t _dfa_id;
    int _alert;
};
struct IDS{
    struct aho_dfa dfa_arr[AHO_MAX_DFA];
    struct stat_t *stats;

};
struct IDS glb_ids;
struct mp_list_t {
    int num_match;
    uint16_t ptrn_id[MAX_MATCH];
};
void init_automataState(struct ids_flow_state* state){
      srand((unsigned)time(NULL));
      state->_state=0;
      state->_alert=false;
      state->_dfa_id=rand()%AHO_MAX_DFA;
}

void parse_pkt(char*buf, int len, struct ids_flow_state* state,struct aho_pkt*  aho_pkt){

    aho_pkt->content=(uint8_t*)malloc(len);
    memcpy(aho_pkt->content,buf,len);
    aho_pkt->dfa_id=state->_dfa_id;
    aho_pkt->len=len;
}

void process_batch(const struct aho_dfa *dfa_arr,
    const struct aho_pkt *pkts, struct mp_list_t *mp_list, struct ids_flow_state* ips_state)
{
    int I, j;

    for(I = 0; I < BATCH_SIZE; I++) {
        int dfa_id = pkts[I].dfa_id;
        int len = pkts[I].len;
        struct aho_state *st_arr = dfa_arr[dfa_id].root;

        int state = ips_state->_state;
      if(state>=dfa_arr[dfa_id].num_used_states){
          ips_state->_alert=false;
          ips_state->_state=state;
          return;
      }


        for(j = 0; j < len; j++) {

            int count = st_arr[state].output.count;

            if(count != 0) {
                /* This state matches some patterns: copy the pattern IDs
                  *  to the output */
                int offset = mp_list[I].num_match;
                memcpy(&mp_list[I].ptrn_id[offset],
                    st_arr[state].out_arr, count * sizeof(uint16_t));
                mp_list[I].num_match += count;
                ips_state->_alert=true;
                ips_state->_state=state;
                return;

            }
            int inp = pkts[I].content[j];
            state = st_arr[state].G[inp];
        }
        ips_state->_state=state;
    }


}
void ids_func(struct aho_ctrl_blk *cb,struct ids_flow_state* state)
{
    int i, j;



    struct aho_dfa *dfa_arr = cb->dfa_arr;
    struct aho_pkt *pkts = cb->pkts;
    int num_pkts = cb->num_pkts;

    /* Per-batch matched patterns */
    struct mp_list_t mp_list[BATCH_SIZE];
    for(i = 0; i < BATCH_SIZE; i++) {
        mp_list[i].num_match = 0;
    }

    /* Being paranoid about GCC optimization: ensure that the memcpys in
      *  process_batch functions don't get optimized out */


    //int tot_proc = 0;     /* How many packets did we actually match ? */
    //int tot_success = 0;  /* Packets that matched a DFA state */
    // tot_bytes = 0;       /* Total bytes matched through DFAs */

    for(i = 0; i < num_pkts; i += BATCH_SIZE) {
        process_batch(dfa_arr, &pkts[i], mp_list,state);

        for(j = 0; j < BATCH_SIZE; j++) {

            mp_list[j].num_match = 0;
        }
    }



}
void ips_detect(char*buf, int len, struct ids_flow_state* state){

    struct aho_pkt* pkts=(struct aho_pkt* )malloc(sizeof(struct aho_pkt));
    parse_pkt(buf, len, state,pkts);
    struct aho_ctrl_blk worker_cb;
    worker_cb.stats = glb_ids.stats;
    worker_cb.tot_threads = 1;
    worker_cb.tid = 0;
    worker_cb.dfa_arr = glb_ids.dfa_arr;
    worker_cb.pkts = pkts;
    worker_cb.num_pkts = 1;

    ids_func(&worker_cb,state);
    free(pkts->content);
    free(pkts);

}

void InitIDS(struct IDS* ids){

    int num_patterns, i;

    int num_threads = 1;
    assert(num_threads >= 1 && num_threads <= AHO_MAX_THREADS);

    ids->stats =(struct stat_t*)malloc(num_threads * sizeof(struct stat_t));
    for(i = 0; i < num_threads; i++) {
        ids->stats[i].tput = 0;
    }
    struct aho_pattern *patterns;
    /* Thread structures */
    //pthread_t worker_threads[AHO_MAX_THREADS];


    red_printf("State size = %lu\n", sizeof(struct aho_state));

    /* Initialize the shared DFAs */
    for(i = 0; i < AHO_MAX_DFA; i++) {
        printf("Initializing DFA %d\n", i);
        aho_init(&(ids->dfa_arr[i]), i);
    }

    red_printf("Adding patterns to DFAs\n");
    patterns = aho_get_patterns(AHO_PATTERN_FILE,
        &num_patterns);

    for(i = 0; i < num_patterns; i++) {
        int dfa_id = patterns[i].dfa_id;
        aho_add_pattern(&(ids->dfa_arr[dfa_id]), &patterns[i], i);
    }

    red_printf("Building AC failure function\n");
    for(i = 0; i < AHO_MAX_DFA; i++) {
        aho_build_ff(&(ids->dfa_arr[i]));
        aho_preprocess_dfa(&(ids->dfa_arr[i]));
    }
}


static void
ApplyActionPerFlow(mctx_t mctx, int msock, int side,
                     uint64_t events, filter_arg_t *arg)

{
    /* this function is called at the first SYN */

    struct ids_flow_state* fs=NULL;
    struct tcp_ring_fragment tcp_flow_off;
    socklen_t intlen = sizeof(int);
    int optval = 0;
    char buf[1000];

    if (mtcp_getsockopt(mctx, msock, SOL_MONSOCKET, MOS_FRAGINFO_CLIBUF, (void *)&tcp_flow_off, &intlen) < 0)
        EXIT_WITH_ERROR("Failed to get packet context!\n");
    fs=(struct ids_flow_state*)mtcp_get_uctx(mctx, msock);
    if(fs==NULL){
        EXIT_WITH_ERROR("Failed to get uctx!\n");
    }

    if (fs->_alert == true) {
        mtcp_setsockopt(mctx, msock,SOL_MONSOCKET, MOS_STOP_MON , &optval, sizeof(optval));
    } else {
        mtcp_ppeek(mctx, msock, side, buf ,tcp_flow_off.len, tcp_flow_off.offset);
        ips_detect(buf,tcp_flow_off.len, fs);
        if(fs->_alert == true){
            mtcp_setsockopt(mctx, msock,SOL_MONSOCKET, MOS_STOP_MON , &optval, sizeof(optval));
        }
    }
}



static void
ApplyActionInitFlow(mctx_t mctx, int msock, int side,
                     uint64_t events, filter_arg_t *arg)

{
    /* this function is called at the first SYN */
    char buf[1000];
    socklen_t intlen = sizeof(int);
    struct tcp_ring_fragment tcp_flow_off;
    int optval = 0;
    struct ids_flow_state* fs=(struct ids_flow_state*)malloc(sizeof(struct ids_flow_state));
    init_automataState(fs);
    mtcp_set_uctx(mctx, msock, (void*)fs);

    if (mtcp_getsockopt(mctx, msock, SOL_MONSOCKET, MOS_FRAGINFO_CLIBUF, (void *)&tcp_flow_off, &intlen) < 0)
        EXIT_WITH_ERROR("Failed to get packet context!\n");
    mtcp_ppeek(mctx, msock, side, buf ,tcp_flow_off.len, tcp_flow_off.offset);
    ips_detect(buf,tcp_flow_off.len, fs);

    /* look up the firewall rules */


    if (fs->_alert == true) {
        mtcp_setsockopt(mctx, msock,SOL_MONSOCKET, MOS_STOP_MON , &optval, sizeof(optval));
    }
}
/*void String_to_eth(char* mac_addr, char* str){
    if (sscanf(str, "%x:%x:%x:%x:%x:%x",
               &mac_addr[0],
               &mac_addr[1],
               &mac_addr[2],
               &mac_addr[3],
               &mac_addr[4],
               &mac_addr[5]) < 6)
    {
        EXIT_WITH_ERROR("Failed to convert mac addr!\n");
    }
}
*/


static void
Change_eth_addr(mctx_t mctx, int msock, int side,
        uint64_t events, filter_arg_t *arg)

{
    /* this function is called at the first SYN */
    printf("received pkt!\n");

    if(side == MOS_SIDE_CLI){
        char mac_dst_str[6]={0x3c, 0xfd, 0xfe, 0x06, 0x07, 0x82};
        char mac_src_str[6]={0x3c, 0xfd, 0xfe, 0x06, 0x09, 0x62};
        mtcp_setlastpkt(mctx, msock, side, 0,
                        (uint8_t*)mac_dst_str, 6, MOS_ETH_HDR | MOS_OVERWRITE);
        mtcp_setlastpkt(mctx, msock, side, 6,
                        (uint8_t*)mac_src_str, 6, MOS_ETH_HDR | MOS_OVERWRITE);
    }else if(side == MOS_SIDE_SVR){
        char mac_dst_str[6]={0x3c, 0xfd, 0xfe, 0x06, 0x08, 0x00};
        char mac_src_str[6]={0x3c, 0xfd, 0xfe, 0x06, 0x09, 0x60};
        mtcp_setlastpkt(mctx, msock, side, 0,
                        (uint8_t*)mac_dst_str, 6, MOS_ETH_HDR | MOS_OVERWRITE);
        mtcp_setlastpkt(mctx, msock, side, 6,
                        (uint8_t*)mac_src_str, 6, MOS_ETH_HDR | MOS_OVERWRITE);
    }

}


/*----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------*/


static void
CreateAndInitThreadContext(struct thread_context* ctx, 
                              int core)
{


    ctx->mctx = mtcp_create_context(core);

    /* create socket  */
    ctx->mon_listener = mtcp_socket(ctx->mctx, AF_INET,
                    MOS_SOCK_MONITOR_STREAM, 0);
    if (ctx->mon_listener < 0)
        EXIT_WITH_ERROR("Failed to create monitor listening socket!\n");

    /* register callback */
    if (mtcp_register_callback(ctx->mctx, ctx->mon_listener,
                               MOS_ON_CONN_START,
                               MOS_HK_SND,
                               ApplyActionInitFlow) == -1)
        EXIT_WITH_ERROR("Failed to register callback func!\n");
    if (mtcp_register_callback(ctx->mctx, ctx->mon_listener,
                               MOS_ON_CONN_NEW_DATA,
                               MOS_NULL,
                               ApplyActionPerFlow) == -1)
        EXIT_WITH_ERROR("Failed to register callback func!\n");


    if (mtcp_register_callback(ctx->mctx, ctx->mon_listener,
                               MOS_ON_PKT_IN,
                               MOS_HK_RCV,
                               Change_eth_addr) == -1)
        EXIT_WITH_ERROR("Failed to register callback func!\n");

    /* CPU 0 is in charge of printing stats */
 //   if (ctx->mctx->cpu == 0 &&
 //       mtcp_settimer(ctx->mctx, ctx->mon_listener,
 //                     &tv_1sec, DumpFWRuleTable))
 //       EXIT_WITH_ERROR("Failed to register timer callback func!\n");

}



/*----------------------------------------------------------------------------*/
static void
WaitAndCleanupThreadContext(struct thread_context* ctx)
{
    /* wait for the TCP thread to finish */
    mtcp_app_join(ctx->mctx);

    /* close the monitoring socket */
    mtcp_close(ctx->mctx, ctx->mon_listener);

    /* tear down */
    mtcp_destroy_context(ctx->mctx);
}
/*----------------------------------------------------------------------------*/




int
main(int argc, char **argv)
{
    int ret, i;
    char *fname = MOS_CONFIG_FILE; /* path to the default mos config file */
    struct mtcp_conf mcfg;
    char simple_firewall_file[1024] = "config/simple_firewall.conf";
    struct thread_context ctx[MAX_CPUS] = {{0}}; /* init all fields to 0 */


    int num_cpus;
    int opt, rc;

    /* get the total # of cpu cores */
    num_cpus = GetNumCPUs();

    while ((opt = getopt(argc, argv, "c:f:n:")) != -1) {
        switch (opt) {
            case 'c':
                fname = optarg;
                break;
                case 'f':
                strcpy(simple_firewall_file, optarg);
                break;
            case 'n':
                if ((rc=atoi(optarg)) > num_cpus) {
                    EXIT_WITH_ERROR("Available number of CPU cores is %d "
                            "while requested cores is %d\n",
                            num_cpus, rc);
                }
                num_cpus = rc;
                break;
            default:
                printf("Usage: %s [-c mos_config_file] "
                       "[-f simple_firewall_config_file]\n",
                       argv[0]);
                return 0;
        }
    }

    InitIDS(&glb_ids);

    /* parse mos configuration file */
    ret = mtcp_init(fname);
    if (ret)
        EXIT_WITH_ERROR("Failed to initialize mtcp.\n");

    /* set the core limit */
    mtcp_getconf(&mcfg);
    mcfg.num_cores = num_cpus;
    mtcp_setconf(&mcfg);

    /* parse simple firewall-specfic startup file */
    ParseConfigFile(simple_firewall_file);

    /* populate local mos-specific mcfg struct for later usage */
    mtcp_getconf(&mcfg);

    /* event for the initial SYN packet */

    /* initialize monitor threads */
    for (i = 0; i < mcfg.num_cores; i++)
        CreateAndInitThreadContext(&ctx[i], i);

    /* wait until all threads finish */
    for (i = 0; i < mcfg.num_cores; i++) {
        WaitAndCleanupThreadContext(&ctx[i]);
        TRACE_INFO("Message test thread %d joined.\n", i);
    }

    mtcp_destroy();

    return EXIT_SUCCESS;
}
/*----------------------------------------------------------------------------*/
