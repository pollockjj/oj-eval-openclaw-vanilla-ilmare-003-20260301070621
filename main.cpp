#include <cstdio>
#include <cstring>
#include <algorithm>
#include <vector>
#include <string>
#include <unordered_map>

using namespace std;

static const int MAXN = 10001;
static const int MAXP = 26;

struct FrozenSub {
    int status;
    int time;
};

struct ProblemState {
    int attempts_before_ac = 0;
    int ac_time = -1;
    bool solved = false;
    bool is_frozen = false;
    int frozen_count = 0;
    vector<FrozenSub> frozen_subs;
};

struct SubInfo {
    int problem;
    int status;
    int time;
};

struct RankKey {
    int neg_solved;
    int penalty;
    int stimes[MAXP];
};

struct Team {
    char name[22];
    ProblemState probs[MAXP];
    RankKey key;
    int frozen_prob_count; // number of frozen problems
    
    vector<SubInfo> all_subs;
    int last_any;
    int last_by_prob[MAXP];
    int last_by_status[4];
    int last_by_both[MAXP][4];
    
    void init() {
        key.neg_solved = 0;
        key.penalty = 0;
        frozen_prob_count = 0;
        for (int i = 0; i < MAXP; i++) key.stimes[i] = 1000000;
        last_any = -1;
        memset(last_by_prob, -1, sizeof(last_by_prob));
        memset(last_by_status, -1, sizeof(last_by_status));
        memset(last_by_both, -1, sizeof(last_by_both));
    }
    
    void add_sub(int prob, int status, int time) {
        int idx = (int)all_subs.size();
        all_subs.push_back({prob, status, time});
        last_any = idx;
        last_by_prob[prob] = idx;
        last_by_status[status] = idx;
        last_by_both[prob][status] = idx;
    }
    
    void recalculate(int pc) {
        int sc = 0;
        key.penalty = 0;
        int cnt = 0;
        for (int i = 0; i < pc; i++) {
            if (probs[i].solved && !probs[i].is_frozen) {
                key.stimes[cnt++] = probs[i].ac_time;
                sc++;
                key.penalty += 20 * probs[i].attempts_before_ac + probs[i].ac_time;
            }
        }
        key.neg_solved = -sc;
        sort(key.stimes, key.stimes + cnt, greater<int>());
        for (int i = cnt; i < MAXP; i++) key.stimes[i] = 1000000;
    }
};

Team teams[MAXN];
int n_teams = 0;
unordered_map<string, int> team_index;

int ranking[MAXN];
int rank_pos[MAXN];
int problem_count = 0;
bool competition_started = false;
bool is_frozen = false;
bool dirty[MAXN];
int tmp_clean[MAXN], tmp_dirty[MAXN];

const char* status_strs[] = {"Accepted", "Wrong_Answer", "Runtime_Error", "Time_Limit_Exceed"};

inline int parse_status(const char* s) {
    if (s[0] == 'A') return 0;
    if (s[0] == 'W') return 1;
    if (s[0] == 'R') return 2;
    return 3;
}

inline bool rank_cmp(int a, int b) {
    const RankKey& ka = teams[a].key;
    const RankKey& kb = teams[b].key;
    if (ka.neg_solved != kb.neg_solved) return ka.neg_solved < kb.neg_solved;
    if (ka.penalty != kb.penalty) return ka.penalty < kb.penalty;
    int sc = -ka.neg_solved;
    for (int i = 0; i < sc; i++) {
        if (ka.stimes[i] != kb.stimes[i]) return ka.stimes[i] < kb.stimes[i];
    }
    return strcmp(teams[a].name, teams[b].name) < 0;
}

void rebuild_rank_pos() {
    for (int i = 0; i < n_teams; i++) rank_pos[ranking[i]] = i;
}

void do_flush() {
    for (int i = 0; i < n_teams; i++) {
        if (dirty[i]) teams[i].recalculate(problem_count);
    }
    
    int nc = 0, nd = 0;
    for (int i = 0; i < n_teams; i++) {
        int tidx = ranking[i];
        if (dirty[tidx]) tmp_dirty[nd++] = tidx;
        else tmp_clean[nc++] = tidx;
    }
    
    memset(dirty, 0, sizeof(bool) * n_teams);
    
    sort(tmp_dirty, tmp_dirty + nd, rank_cmp);
    
    int ic = 0, id = 0, ir = 0;
    while (ic < nc && id < nd) {
        if (rank_cmp(tmp_clean[ic], tmp_dirty[id]))
            ranking[ir++] = tmp_clean[ic++];
        else
            ranking[ir++] = tmp_dirty[id++];
    }
    while (ic < nc) ranking[ir++] = tmp_clean[ic++];
    while (id < nd) ranking[ir++] = tmp_dirty[id++];
    
    rebuild_rank_pos();
}

void print_problem(const ProblemState& ps) {
    if (ps.is_frozen) {
        if (ps.attempts_before_ac == 0)
            printf(" 0/%d", ps.frozen_count);
        else
            printf(" -%d/%d", ps.attempts_before_ac, ps.frozen_count);
        return;
    }
    if (ps.solved) {
        if (ps.attempts_before_ac == 0) printf(" +");
        else printf(" +%d", ps.attempts_before_ac);
        return;
    }
    if (ps.attempts_before_ac == 0) printf(" .");
    else printf(" -%d", ps.attempts_before_ac);
}

void print_scoreboard() {
    for (int i = 0; i < n_teams; i++) {
        Team& t = teams[ranking[i]];
        printf("%s %d %d %d", t.name, i + 1, -t.key.neg_solved, t.key.penalty);
        for (int j = 0; j < problem_count; j++) print_problem(t.probs[j]);
        putchar('\n');
    }
}

// Unfreeze a problem. Returns true if AC was found.
bool unfreeze_problem(Team& t, int fp) {
    ProblemState& ps = t.probs[fp];
    ps.is_frozen = false;
    t.frozen_prob_count--;
    bool got_ac = false;
    for (auto& fs : ps.frozen_subs) {
        if (!ps.solved) {
            if (fs.status == 0) {
                ps.solved = true;
                ps.ac_time = fs.time;
                got_ac = true;
            } else {
                ps.attempts_before_ac++;
            }
        }
    }
    ps.frozen_subs.clear();
    ps.frozen_count = 0;
    return got_ac;
}

char buf[64];

int main() {
    memset(dirty, 0, sizeof(dirty));
    
    while (scanf("%s", buf) == 1) {
        if (buf[0] == 'A' && buf[1] == 'D') {
            char name[22];
            scanf("%s", name);
            if (competition_started) {
                printf("[Error]Add failed: competition has started.\n");
            } else if (team_index.count(name)) {
                printf("[Error]Add failed: duplicated team name.\n");
            } else {
                int idx = n_teams++;
                team_index[name] = idx;
                teams[idx].init();
                strcpy(teams[idx].name, name);
                ranking[idx] = idx;
                printf("[Info]Add successfully.\n");
            }
        } else if (buf[0] == 'S' && buf[1] == 'T' && buf[2] == 'A') {
            int dt, pc;
            scanf("%s %d %s %d", buf, &dt, buf, &pc);
            if (competition_started) {
                printf("[Error]Start failed: competition has started.\n");
            } else {
                problem_count = pc;
                competition_started = true;
                sort(ranking, ranking + n_teams, [](int a, int b) {
                    return strcmp(teams[a].name, teams[b].name) < 0;
                });
                rebuild_rank_pos();
                printf("[Info]Competition starts.\n");
            }
        } else if (buf[0] == 'S' && buf[1] == 'U') {
            char prob_s[4], team_name[22], status_s[22];
            int time_val;
            scanf("%s %s %s %s %s %s %d", prob_s, buf, team_name, buf, status_s, buf, &time_val);
            
            int prob = prob_s[0] - 'A';
            int status = parse_status(status_s);
            int tidx = team_index[team_name];
            Team& t = teams[tidx];
            
            t.add_sub(prob, status, time_val);
            
            ProblemState& ps = t.probs[prob];
            if (is_frozen && !ps.solved) {
                if (!ps.is_frozen) {
                    ps.is_frozen = true;
                    t.frozen_prob_count++;
                }
                ps.frozen_count++;
                ps.frozen_subs.push_back({status, time_val});
            } else if (!ps.solved) {
                if (status == 0) {
                    ps.solved = true;
                    ps.ac_time = time_val;
                } else {
                    ps.attempts_before_ac++;
                }
            }
            dirty[tidx] = true;
        } else if (buf[0] == 'F' && buf[1] == 'L') {
            printf("[Info]Flush scoreboard.\n");
            do_flush();
        } else if (buf[0] == 'F' && buf[1] == 'R') {
            if (is_frozen) {
                printf("[Error]Freeze failed: scoreboard has been frozen.\n");
            } else {
                is_frozen = true;
                printf("[Info]Freeze scoreboard.\n");
            }
        } else if (buf[0] == 'S' && buf[1] == 'C' && buf[2] == 'R') {
            if (!is_frozen) {
                printf("[Error]Scroll failed: scoreboard has not been frozen.\n");
            } else {
                printf("[Info]Scroll scoreboard.\n");
                do_flush();
                print_scoreboard();
                
                // Optimized scroll: use pointer, skip non-AC unfreezes
                int check_from = n_teams - 1;
                while (check_from >= 0) {
                    // Find lowest-ranked team with frozen problems
                    int r = -1;
                    for (int i = check_from; i >= 0; i--) {
                        if (teams[ranking[i]].frozen_prob_count > 0) {
                            r = i;
                            break;
                        }
                    }
                    if (r == -1) break;
                    
                    int tidx = ranking[r];
                    Team& t = teams[tidx];
                    bool moved = false;
                    
                    while (t.frozen_prob_count > 0) {
                        // Find smallest frozen problem
                        int fp = -1;
                        for (int p = 0; p < problem_count; p++) {
                            if (t.probs[p].is_frozen) { fp = p; break; }
                        }
                        
                        bool got_ac = unfreeze_problem(t, fp);
                        
                        if (got_ac) {
                            t.recalculate(problem_count);
                            
                            // Binary search for new position
                            // Team can only move up (lower index = better rank)
                            // Linear scan up from r-1 (often quick)
                            int new_rank = r;
                            while (new_rank > 0 && rank_cmp(tidx, ranking[new_rank - 1])) {
                                new_rank--;
                            }
                            
                            if (new_rank < r) {
                                int replaced = ranking[new_rank];
                                // Shift and update rank_pos
                                for (int i = r; i > new_rank; i--) {
                                    ranking[i] = ranking[i - 1];
                                    rank_pos[ranking[i]] = i;
                                }
                                ranking[new_rank] = tidx;
                                rank_pos[tidx] = new_rank;
                                
                                printf("%s %s %d %d\n", t.name, teams[replaced].name,
                                       -t.key.neg_solved, t.key.penalty);
                                
                                // After move, restart scan from r (teams shifted down)
                                check_from = r;
                                moved = true;
                                break;
                            }
                        }
                    }
                    
                    if (!moved) {
                        // Team fully unfrozen without moving, continue upward
                        check_from = r - 1;
                    }
                }
                
                print_scoreboard();
                is_frozen = false;
            }
        } else if (buf[0] == 'Q' && buf[6] == 'R') {
            char name[22];
            scanf("%s", name);
            auto it = team_index.find(name);
            if (it == team_index.end()) {
                printf("[Error]Query ranking failed: cannot find the team.\n");
            } else {
                printf("[Info]Complete query ranking.\n");
                if (is_frozen)
                    printf("[Warning]Scoreboard is frozen. The ranking may be inaccurate until it were scrolled.\n");
                printf("%s NOW AT RANKING %d\n", name, rank_pos[it->second] + 1);
            }
        } else if (buf[0] == 'Q' && buf[6] == 'S') {
            char team_name[22], prob_part[32], status_part[32];
            scanf("%s %s %s %s %s", team_name, buf, prob_part, buf, status_part);
            
            char* prob_val = prob_part + 8;
            char* stat_val = status_part + 7;
            
            auto it = team_index.find(team_name);
            if (it == team_index.end()) {
                printf("[Error]Query submission failed: cannot find the team.\n");
            } else {
                printf("[Info]Complete query submission.\n");
                int tidx = it->second;
                Team& t = teams[tidx];
                
                bool prob_all = (strcmp(prob_val, "ALL") == 0);
                bool stat_all = (strcmp(stat_val, "ALL") == 0);
                
                int last_idx = -1;
                if (prob_all && stat_all) {
                    last_idx = t.last_any;
                } else if (prob_all) {
                    last_idx = t.last_by_status[parse_status(stat_val)];
                } else if (stat_all) {
                    last_idx = t.last_by_prob[prob_val[0] - 'A'];
                } else {
                    last_idx = t.last_by_both[prob_val[0] - 'A'][parse_status(stat_val)];
                }
                
                if (last_idx == -1) {
                    printf("Cannot find any submission.\n");
                } else {
                    SubInfo& s = t.all_subs[last_idx];
                    printf("%s %c %s %d\n", team_name, 'A' + s.problem, status_strs[s.status], s.time);
                }
            }
        } else if (buf[0] == 'E') {
            printf("[Info]Competition ends.\n");
            break;
        }
    }
    return 0;
}
