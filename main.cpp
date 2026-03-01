#include <cstdio>
#include <cstring>
#include <algorithm>
#include <vector>
#include <unordered_map>
#include <string>

using namespace std;

static const int MAXN = 10001;
static const int MAXP = 26;
static const int BIG = 1000000;

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
    int stimes[MAXP]; // sorted desc, padded with BIG
};

struct Team {
    char name[22];
    ProblemState probs[MAXP];
    RankKey key;
    int frozen_prob_count;
    
    vector<SubInfo> all_subs;
    int last_any;
    int last_by_prob[MAXP];
    int last_by_status[4];
    int last_by_both[MAXP][4];
    
    void init() {
        key.neg_solved = 0;
        key.penalty = 0;
        frozen_prob_count = 0;
        for (int i = 0; i < MAXP; i++) key.stimes[i] = BIG;
        last_any = -1;
        memset(last_by_prob, -1, sizeof(last_by_prob));
        memset(last_by_status, -1, sizeof(last_by_status));
        memset(last_by_both, -1, sizeof(last_by_both));
    }
    
    void add_sub(int prob, int status, int t) {
        int idx = (int)all_subs.size();
        all_subs.push_back({prob, status, t});
        last_any = idx;
        last_by_prob[prob] = idx;
        last_by_status[status] = idx;
        last_by_both[prob][status] = idx;
    }
    
    void recalculate(int pc) {
        int sc = 0, cnt = 0;
        key.penalty = 0;
        for (int i = 0; i < pc; i++) {
            if (probs[i].solved && !probs[i].is_frozen) {
                key.stimes[cnt++] = probs[i].ac_time;
                sc++;
                key.penalty += 20 * probs[i].attempts_before_ac + probs[i].ac_time;
            }
        }
        key.neg_solved = -sc;
        // Insertion sort since cnt <= 26, often partially sorted
        for (int i = 1; i < cnt; i++) {
            int tmp = key.stimes[i];
            int j = i - 1;
            while (j >= 0 && key.stimes[j] < tmp) {
                key.stimes[j + 1] = key.stimes[j];
                j--;
            }
            key.stimes[j + 1] = tmp;
        }
        for (int i = cnt; i < MAXP; i++) key.stimes[i] = BIG;
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
bool dirty_flag[MAXN];
int tmp_a[MAXN], tmp_b[MAXN];

const char* status_strs[] = {"Accepted", "Wrong_Answer", "Runtime_Error", "Time_Limit_Exceed"};

inline int parse_status(const char* s) {
    switch (s[0]) {
        case 'A': return 0;
        case 'W': return 1;
        case 'R': return 2;
        default: return 3;
    }
}

inline int key_cmp(int a, int b) {
    // Returns <0 if a ranks higher, >0 if b ranks higher, 0 if equal on key (then name)
    const RankKey& ka = teams[a].key;
    const RankKey& kb = teams[b].key;
    if (ka.neg_solved != kb.neg_solved) return ka.neg_solved - kb.neg_solved;
    if (ka.penalty != kb.penalty) return ka.penalty - kb.penalty;
    int sc = -ka.neg_solved;
    for (int i = 0; i < sc; i++) {
        if (ka.stimes[i] != kb.stimes[i]) return ka.stimes[i] - kb.stimes[i];
    }
    return strcmp(teams[a].name, teams[b].name);
}

inline bool rank_cmp(int a, int b) {
    return key_cmp(a, b) < 0;
}

void rebuild_rank_pos() {
    for (int i = 0; i < n_teams; i++) rank_pos[ranking[i]] = i;
}

void do_flush() {
    for (int i = 0; i < n_teams; i++) {
        if (dirty_flag[i]) teams[i].recalculate(problem_count);
    }
    
    int nc = 0, nd = 0;
    for (int i = 0; i < n_teams; i++) {
        int tidx = ranking[i];
        if (dirty_flag[tidx]) tmp_b[nd++] = tidx;
        else tmp_a[nc++] = tidx;
    }
    
    memset(dirty_flag, 0, n_teams);
    
    if (nd > 0) {
        sort(tmp_b, tmp_b + nd, rank_cmp);
        
        int ic = 0, id = 0, ir = 0;
        while (ic < nc && id < nd) {
            if (rank_cmp(tmp_a[ic], tmp_b[id]))
                ranking[ir++] = tmp_a[ic++];
            else
                ranking[ir++] = tmp_b[id++];
        }
        while (ic < nc) ranking[ir++] = tmp_a[ic++];
        while (id < nd) ranking[ir++] = tmp_b[id++];
    }
    
    rebuild_rank_pos();
}

// Output buffer
static char obuf[1 << 22];
static int opos = 0;

inline void oflush() {
    fwrite(obuf, 1, opos, stdout);
    opos = 0;
}

inline void oputc(char c) {
    obuf[opos++] = c;
    if (opos >= (1 << 22) - 256) oflush();
}

inline void oputs(const char* s) {
    while (*s) obuf[opos++] = *s++;
    if (opos >= (1 << 22) - 256) oflush();
}

inline void oputn(int n) {
    if (n < 0) { oputc('-'); n = -n; }
    if (n == 0) { oputc('0'); return; }
    char tmp[12];
    int len = 0;
    while (n > 0) { tmp[len++] = '0' + n % 10; n /= 10; }
    for (int i = len - 1; i >= 0; i--) oputc(tmp[i]);
}

void print_problem(const ProblemState& ps) {
    oputc(' ');
    if (ps.is_frozen) {
        if (ps.attempts_before_ac == 0) {
            oputc('0'); oputc('/'); oputn(ps.frozen_count);
        } else {
            oputc('-'); oputn(ps.attempts_before_ac); oputc('/'); oputn(ps.frozen_count);
        }
        return;
    }
    if (ps.solved) {
        oputc('+');
        if (ps.attempts_before_ac > 0) oputn(ps.attempts_before_ac);
        return;
    }
    if (ps.attempts_before_ac == 0) oputc('.');
    else { oputc('-'); oputn(ps.attempts_before_ac); }
}

void print_scoreboard() {
    for (int i = 0; i < n_teams; i++) {
        Team& t = teams[ranking[i]];
        oputs(t.name); oputc(' '); oputn(i + 1); oputc(' ');
        oputn(-t.key.neg_solved); oputc(' '); oputn(t.key.penalty);
        for (int j = 0; j < problem_count; j++) print_problem(t.probs[j]);
        oputc('\n');
    }
}

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

// Input buffer
static char ibuf[1 << 22];
static int ibufpos = 0, ibuflen = 0;

inline int igetc() {
    if (ibufpos >= ibuflen) {
        ibuflen = fread(ibuf, 1, sizeof(ibuf), stdin);
        ibufpos = 0;
        if (ibuflen == 0) return -1;
    }
    return (unsigned char)ibuf[ibufpos++];
}

inline bool iread(char* s) {
    int c;
    while ((c = igetc()) != -1 && (c == ' ' || c == '\n' || c == '\r'));
    if (c == -1) return false;
    *s++ = c;
    while ((c = igetc()) != -1 && c != ' ' && c != '\n' && c != '\r') *s++ = c;
    *s = 0;
    return true;
}

inline bool ireadint(int& v) {
    int c;
    while ((c = igetc()) != -1 && (c == ' ' || c == '\n' || c == '\r'));
    if (c == -1) return false;
    v = 0;
    bool neg = false;
    if (c == '-') { neg = true; c = igetc(); }
    v = c - '0';
    while ((c = igetc()) != -1 && c >= '0' && c <= '9') v = v * 10 + c - '0';
    if (neg) v = -v;
    return true;
}

char buf[64];

int main() {
    memset(dirty_flag, 0, sizeof(dirty_flag));
    
    while (iread(buf)) {
        if (buf[0] == 'A' && buf[1] == 'D') {
            char name[22];
            iread(name);
            if (competition_started) {
                oputs("[Error]Add failed: competition has started.\n");
            } else if (team_index.count(name)) {
                oputs("[Error]Add failed: duplicated team name.\n");
            } else {
                int idx = n_teams++;
                team_index[name] = idx;
                teams[idx].init();
                strcpy(teams[idx].name, name);
                ranking[idx] = idx;
                oputs("[Info]Add successfully.\n");
            }
        } else if (buf[0] == 'S' && buf[1] == 'T' && buf[2] == 'A') {
            int dt, pc;
            iread(buf); ireadint(dt); iread(buf); ireadint(pc);
            if (competition_started) {
                oputs("[Error]Start failed: competition has started.\n");
            } else {
                problem_count = pc;
                competition_started = true;
                sort(ranking, ranking + n_teams, [](int a, int b) {
                    return strcmp(teams[a].name, teams[b].name) < 0;
                });
                rebuild_rank_pos();
                oputs("[Info]Competition starts.\n");
            }
        } else if (buf[0] == 'S' && buf[1] == 'U') {
            char prob_s[4], team_name[22], status_s[22];
            int time_val;
            iread(prob_s); iread(buf); iread(team_name); iread(buf); iread(status_s); iread(buf); ireadint(time_val);
            
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
            dirty_flag[tidx] = true;
        } else if (buf[0] == 'F' && buf[1] == 'L') {
            oputs("[Info]Flush scoreboard.\n");
            do_flush();
        } else if (buf[0] == 'F' && buf[1] == 'R') {
            if (is_frozen) {
                oputs("[Error]Freeze failed: scoreboard has been frozen.\n");
            } else {
                is_frozen = true;
                oputs("[Info]Freeze scoreboard.\n");
            }
        } else if (buf[0] == 'S' && buf[1] == 'C' && buf[2] == 'R') {
            if (!is_frozen) {
                oputs("[Error]Scroll failed: scoreboard has not been frozen.\n");
            } else {
                oputs("[Info]Scroll scoreboard.\n");
                do_flush();
                print_scoreboard();
                
                int check_from = n_teams - 1;
                while (check_from >= 0) {
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
                        int fp = -1;
                        for (int p = 0; p < problem_count; p++) {
                            if (t.probs[p].is_frozen) { fp = p; break; }
                        }
                        
                        bool got_ac = unfreeze_problem(t, fp);
                        
                        if (got_ac) {
                            t.recalculate(problem_count);
                            
                            // Binary search for new position
                            int lo = 0, hi = r;
                            while (lo < hi) {
                                int mid = (lo + hi) >> 1;
                                if (rank_cmp(tidx, ranking[mid]))
                                    hi = mid;
                                else
                                    lo = mid + 1;
                            }
                            int new_rank = lo;
                            
                            if (new_rank < r) {
                                int replaced = ranking[new_rank];
                                memmove(&ranking[new_rank + 1], &ranking[new_rank], (r - new_rank) * sizeof(int));
                                ranking[new_rank] = tidx;
                                // Update rank_pos for shifted teams
                                for (int i = new_rank; i <= r; i++) rank_pos[ranking[i]] = i;
                                
                                oputs(t.name); oputc(' ');
                                oputs(teams[replaced].name); oputc(' ');
                                oputn(-t.key.neg_solved); oputc(' ');
                                oputn(t.key.penalty); oputc('\n');
                                
                                check_from = r;
                                moved = true;
                                break;
                            }
                        }
                    }
                    
                    if (!moved) {
                        check_from = r - 1;
                    }
                }
                
                print_scoreboard();
                is_frozen = false;
            }
        } else if (buf[0] == 'Q' && buf[6] == 'R') {
            char name[22];
            iread(name);
            auto it = team_index.find(name);
            if (it == team_index.end()) {
                oputs("[Error]Query ranking failed: cannot find the team.\n");
            } else {
                oputs("[Info]Complete query ranking.\n");
                if (is_frozen)
                    oputs("[Warning]Scoreboard is frozen. The ranking may be inaccurate until it were scrolled.\n");
                oputs(name); oputs(" NOW AT RANKING "); oputn(rank_pos[it->second] + 1); oputc('\n');
            }
        } else if (buf[0] == 'Q' && buf[6] == 'S') {
            char team_name[22], prob_part[32], status_part[32];
            iread(team_name); iread(buf); iread(prob_part); iread(buf); iread(status_part);
            
            char* prob_val = prob_part + 8;
            char* stat_val = status_part + 7;
            
            auto it = team_index.find(team_name);
            if (it == team_index.end()) {
                oputs("[Error]Query submission failed: cannot find the team.\n");
            } else {
                oputs("[Info]Complete query submission.\n");
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
                    oputs("Cannot find any submission.\n");
                } else {
                    SubInfo& s = t.all_subs[last_idx];
                    oputs(team_name); oputc(' ');
                    oputc('A' + s.problem); oputc(' ');
                    oputs(status_strs[s.status]); oputc(' ');
                    oputn(s.time); oputc('\n');
                }
            }
        } else if (buf[0] == 'E') {
            oputs("[Info]Competition ends.\n");
            break;
        }
    }
    oflush();
    return 0;
}
