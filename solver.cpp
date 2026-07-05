#include <algorithm>
#include <cassert>
#include <climits>
#include <chrono>
#include <cmath>
#include <csignal>
#include <cstdint>
#include <cstdlib>
#include <cctype>
#include <deque>
#include <functional>
#include <iostream>
#include <memory>
#include <numeric>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
using namespace std;

#ifndef VERBOSE
#define VERBOSE 0
#endif

#define VERBOSE_CERR if (VERBOSE) cerr

const uint64_t RANDOM_SEED = 42ULL;
const double TEMP_START = 0.60;
const double TEMP_END = 0.012;
const double PENALTY_WEIGHT = 8.0;
const double SEED_TIME_FRAC = 0.25;
const double SEED_TIME_CAP = 4.0;
const double POLISH_TIME_FRAC = 0.20;
const double POLISH_TIME_CAP = 15.0;
const double DIAG_INTERVAL = 10.0;
const int MOVE_TOGGLE = 18;
const int MOVE_REMOVE = 50;
const int MOVE_ADD = 20;
const int MOVE_PAIR_REMOVE = 5;
const int MOVE_SWAP = 30;
const double MOVE_SWAP_COLD_FACTOR = 2.0;
const int MOVE_SIBLING_SWAP = 5;
const int MOVE_LEVEL_SWAP = 5;
const int SWAP_TREES = 1;
const int REDUCE_CHAIN = 1;
const int REDUCE_THREE_TWO = 1;
const int CLUSTER_MIN_N = 50;
const int CLUSTER_MIN_SIDE = 10;
const double CLUSTER_MIN_FRAC = 0.01;
const int CLUSTER_MAX_DEPTH = 5;
const int CLUSTER_MAX_BLOCKS = 256;
const double CLUSTER_GLOBAL_MERGE_CAP = 1.0;
const int EARLY_SPLIT_THRESHOLD = 500;
const int EARLY_SPLIT_CUTS = 2;
const int NUM_RESTARTS = 2;
const double RESTART_PERTURB_FRAC = 0.05;
const int RESTART_MIN_N = 800;

static volatile sig_atomic_t g_stop = 0;

static void handle_signal(int) {
    g_stop = 1;
}

struct Timer {
    chrono::steady_clock::time_point start = chrono::steady_clock::now();
    double limit_seconds = 300.0;

    explicit Timer(double limit) : limit_seconds(limit) {}

    double elapsed() const {
        return chrono::duration<double>(chrono::steady_clock::now() - start).count();
    }

    bool expired() const {
        return g_stop || elapsed() >= limit_seconds;
    }
};

struct FlatHashMap {
    static constexpr uint64_t EMPTY = ~0ULL;
    vector<uint64_t> keys;
    vector<int> vals;
    int mask = 0;
    int fill = 0;

    void init(int cap_hint) {
        int sz = 16;
        while (sz < cap_hint * 2) sz <<= 1;
        mask = sz - 1;
        keys.assign(sz, EMPTY);
        vals.assign(sz, 0);
        fill = 0;
    }

    void grow() {
        vector<uint64_t> old_keys = move(keys);
        vector<int> old_vals = move(vals);
        int new_sz = (mask + 1) * 2;
        mask = new_sz - 1;
        keys.assign(new_sz, EMPTY);
        vals.assign(new_sz, 0);
        fill = 0;
        for (int i = 0; i < (int)old_keys.size(); ++i) {
            if (old_keys[i] == EMPTY) continue;
            int pos = int((old_keys[i] * 0x9e3779b97f4a7c15ULL) >> 32) & mask;
            while (keys[pos] != EMPTY) pos = (pos + 1) & mask;
            keys[pos] = old_keys[i];
            vals[pos] = old_vals[i];
            ++fill;
        }
    }

    int find(uint64_t key) const {
        int pos = int((key * 0x9e3779b97f4a7c15ULL) >> 32) & mask;
        while (keys[pos] != EMPTY && keys[pos] != key) pos = (pos + 1) & mask;
        return (keys[pos] == key) ? vals[pos] : -1;
    }

    void insert(uint64_t key, int val) {
        if (fill * 2 > mask) grow();
        int pos = int((key * 0x9e3779b97f4a7c15ULL) >> 32) & mask;
        while (keys[pos] != EMPTY) pos = (pos + 1) & mask;
        keys[pos] = key;
        vals[pos] = val;
        ++fill;
    }

};

struct Interner {
    int n = 0;
    vector<pair<int, int>> child;
    FlatHashMap ids;

    void reset(int leaves) {
        n = leaves;
        child.assign(n + 1, {0, 0});
        int cap_base = max(1, n);
        if (n < 5000) {
            child.reserve(8 * cap_base + 1);
            ids.init(8 * cap_base);
        } else {
            ids.init(4 * cap_base);
        }
    }

    int intern(int a, int b) {
        if (a > b) swap(a, b);
        uint64_t key = (uint64_t(uint32_t(a)) << 32) | uint32_t(b);
        int existing = ids.find(key);
        if (existing >= 0) return existing;
        int id = int(child.size());
        child.push_back({a, b});
        ids.insert(key, id);
        return id;
    }

    string to_newick(int id) const {
        if (id <= n) return to_string(id);
        auto [a, b] = child[id];
        return "(" + to_newick(a) + "," + to_newick(b) + ")";
    }
};

struct Fenwick {
    int n = 0;
    vector<int> bit;

    explicit Fenwick(int size = 0) { reset(size); }

    void reset(int size) {
        n = size;
        bit.assign(n + 1, 0);
    }

    void add(int idx, int delta) {
        for (; idx <= n; idx += idx & -idx) bit[idx] += delta;
    }

    int sum_prefix(int idx) const {
        int res = 0;
        for (; idx > 0; idx -= idx & -idx) res += bit[idx];
        return res;
    }

    int sum_range(int l, int r) const {
        return l <= r ? sum_prefix(r) - sum_prefix(l - 1) : 0;
    }
};

struct Tree {
    struct Node {
        int left = -1, right = -1, parent = -1, label = 0;
    };

    struct Analysis {
        int id = 0;
        vector<int> edges;
    };

    int n = 0, root = -1, logn = 0;
    vector<Node> nodes;
    vector<int> leaf_node, tin, tout, depth, leaf_order, leaf_rank;
    vector<int> leaf_l, leaf_r, leaf_count, subtree_id;
    vector<vector<int>> up;

    bool is_leaf(int v) const { return nodes[v].label != 0; }

    static Tree parse_newick(const string& s, int leaves) {
        Tree t;
        t.n = leaves;
        t.leaf_node.assign(leaves + 1, -1);
        size_t pos = 0;

        function<int()> parse_rec = [&]() -> int {
            if (s[pos] == '(') {
                ++pos;
                int a = parse_rec();
                if (pos < s.size() && s[pos] == ',') ++pos;
                int b = parse_rec();
                if (pos < s.size() && s[pos] == ')') ++pos;
                int id = int(t.nodes.size());
                t.nodes.push_back({a, b, -1, 0});
                t.nodes[a].parent = id;
                t.nodes[b].parent = id;
                return id;
            }
            int label = 0;
            while (pos < s.size() && s[pos] >= '0' && s[pos] <= '9') {
                label = label * 10 + (s[pos] - '0');
                ++pos;
            }
            int id = int(t.nodes.size());
            t.nodes.push_back({-1, -1, -1, label});
            if (1 <= label && label <= leaves) t.leaf_node[label] = id;
            return id;
        };

        t.root = parse_rec();
        return t;
    }

    void preprocess(Interner& interner) {
        int m = int(nodes.size());
        logn = 1;
        while ((1 << logn) <= max(1, m)) ++logn;
        tin.assign(m, 0);
        tout.assign(m, 0);
        depth.assign(m, 0);
        up.assign(logn, vector<int>(m, root));
        leaf_order.clear();
        leaf_order.reserve(n);
        leaf_rank.assign(n + 1, 0);
        leaf_l.assign(m, 0);
        leaf_r.assign(m, 0);
        leaf_count.assign(m, 0);
        subtree_id.assign(m, 0);

        int timer = 0;
        vector<pair<int, int>> st;
        st.reserve(2 * m);
        nodes[root].parent = root;
        up[0][root] = root;
        st.push_back({root, 0});

        while (!st.empty()) {
            auto [v, state] = st.back();
            st.pop_back();
            if (state == 0) {
                tin[v] = timer++;
                for (int j = 1; j < logn; ++j) up[j][v] = up[j - 1][up[j - 1][v]];
                st.push_back({v, 1});
                if (!is_leaf(v)) {
                    int l = nodes[v].left;
                    int r = nodes[v].right;
                    nodes[l].parent = v;
                    nodes[r].parent = v;
                    depth[l] = depth[r] = depth[v] + 1;
                    up[0][l] = up[0][r] = v;
                    st.push_back({r, 0});
                    st.push_back({l, 0});
                }
            } else {
                tout[v] = timer;
                if (is_leaf(v)) {
                    int label = nodes[v].label;
                    leaf_count[v] = 1;
                    leaf_l[v] = leaf_r[v] = int(leaf_order.size()) + 1;
                    leaf_rank[label] = leaf_l[v];
                    leaf_order.push_back(label);
                    subtree_id[v] = label;
                } else {
                    int l = nodes[v].left, r = nodes[v].right;
                    leaf_count[v] = leaf_count[l] + leaf_count[r];
                    leaf_l[v] = min(leaf_l[l], leaf_l[r]);
                    leaf_r[v] = max(leaf_r[l], leaf_r[r]);
                    subtree_id[v] = interner.intern(subtree_id[l], subtree_id[r]);
                }
            }
        }
    }

    bool ancestor(int a, int b) const {
        return tin[a] <= tin[b] && tout[b] <= tout[a];
    }

    int lca(int a, int b) const {
        if (ancestor(a, b)) return a;
        if (ancestor(b, a)) return b;
        int x = a;
        for (int j = logn - 1; j >= 0; --j) {
            int y = up[j][x];
            if (!ancestor(y, b)) x = y;
        }
        return up[0][x];
    }

    vector<int> labels_by_tin(vector<int> labels) const {
        sort(labels.begin(), labels.end(), [&](int a, int b) {
            return tin[leaf_node[a]] < tin[leaf_node[b]];
        });
        return labels;
    }

    vector<int> collect_leaves(int node) const {
        vector<int> labels;
        labels.reserve(leaf_count[node]);
        vector<int> st = {node};
        while (!st.empty()) {
            int v = st.back();
            st.pop_back();
            if (is_leaf(v)) {
                labels.push_back(nodes[v].label);
            } else {
                st.push_back(nodes[v].right);
                st.push_back(nodes[v].left);
            }
        }
        sort(labels.begin(), labels.end());
        return labels;
    }

    Analysis analyze_sorted_labels(const vector<int>& labels_sorted_by_tin,
                                   Interner& interner,
                                   bool need_edges) const {
        Analysis result;
        int k = int(labels_sorted_by_tin.size());
        if (k == 0) return result;
        if (k == 1) {
            result.id = labels_sorted_by_tin[0];
            return result;
        }

        vector<int> all;
        all.reserve(2 * k);
        for (int label : labels_sorted_by_tin) all.push_back(leaf_node[label]);
        for (int i = 0; i + 1 < k; ++i) {
            int a = leaf_node[labels_sorted_by_tin[i]];
            int b = leaf_node[labels_sorted_by_tin[i + 1]];
            all.push_back(lca(a, b));
        }
        sort(all.begin(), all.end(), [&](int a, int b) { return tin[a] < tin[b]; });
        all.erase(unique(all.begin(), all.end()), all.end());

        int sz = int(all.size());
        vector<vector<int>> children(sz);
        vector<int> stack;
        stack.reserve(sz);
        for (int i = 0; i < sz; ++i) {
            int v = all[i];
            while (!stack.empty() && !ancestor(all[stack.back()], v)) stack.pop_back();
            if (!stack.empty()) {
                int pidx = stack.back();
                int p = all[pidx];
                children[pidx].push_back(i);
                if (need_edges) {
                    for (int x = v; x != p; x = nodes[x].parent) result.edges.push_back(x);
                }
            }
            stack.push_back(i);
        }

        vector<int> rid(sz, 0);
        for (int i = sz - 1; i >= 0; --i) {
            int v = all[i];
            if (is_leaf(v)) {
                rid[i] = nodes[v].label;
            } else {
                vector<int> cids;
                cids.reserve(children[i].size());
                for (int c : children[i]) {
                    if (rid[c] != 0) cids.push_back(rid[c]);
                }
                if (cids.empty()) rid[i] = 0;
                else if (cids.size() == 1) rid[i] = cids[0];
                else rid[i] = interner.intern(cids[0], cids[1]);
            }
        }

        result.id = rid[0];
        if (need_edges) {
            sort(result.edges.begin(), result.edges.end());
            result.edges.erase(unique(result.edges.begin(), result.edges.end()), result.edges.end());
        }
        return result;
    }
};

struct Component {
    vector<int> labels;
    vector<int> tin_labels[2];
    vector<int> edges[2];
    int id = 0;
    bool active = true;
};

struct ReductionExpansion {
    struct ChainRecord {
        int a = 0, b = 0, c = 0;
        vector<int> deleted_orig;
    };

    bool active = false;
    int original_n = 0;
    vector<string> original_newicks;
    vector<vector<int>> reduced_orig;
    vector<ChainRecord> chains;
    vector<vector<int>> forced_singletons;

    static vector<int> merge_sorted(const vector<int>& a, const vector<int>& b) {
        vector<int> out;
        out.reserve(a.size() + b.size());
        merge(a.begin(), a.end(), b.begin(), b.end(), back_inserter(out));
        return out;
    }

    static void append_sorted(vector<int>& dst, const vector<int>& src) {
        vector<int> out;
        out.reserve(dst.size() + src.size());
        merge(dst.begin(), dst.end(), src.begin(), src.end(), back_inserter(out));
        dst.swap(out);
    }

    static bool shape_for_labels(const Tree trees[2], Interner& interner,
                                 const vector<int>& labels, int& id) {
        if (labels.empty()) return false;
        vector<int> tin0 = trees[0].labels_by_tin(labels);
        vector<int> tin1 = trees[1].labels_by_tin(labels);
        Tree::Analysis a0 = trees[0].analyze_sorted_labels(tin0, interner, false);
        Tree::Analysis a1 = trees[1].analyze_sorted_labels(tin1, interner, false);
        if (a0.id != a1.id) return false;
        id = a0.id;
        return true;
    }

    vector<string> expand_to_newicks(const vector<Component>& reduced_comps) const {
        if (!active) return {};

        Interner out_interner;
        out_interner.reset(original_n);
        Tree original_trees[2] = {
            Tree::parse_newick(original_newicks[0], original_n),
            Tree::parse_newick(original_newicks[1], original_n)
        };
        original_trees[0].preprocess(out_interner);
        original_trees[1].preprocess(out_interner);

        vector<vector<int>> expanded;
        vector<int> reduced_comp(reduced_orig.size(), -1);
        expanded.reserve(reduced_comps.size() + chains.size() + forced_singletons.size());

        for (const Component& comp : reduced_comps) {
            vector<int> labels;
            for (int label : comp.labels) {
                if (label > 0 && label < int(reduced_orig.size())) {
                    append_sorted(labels, reduced_orig[label]);
                }
            }
            if (!labels.empty()) {
                int idx = int(expanded.size());
                for (int label : comp.labels) {
                    if (label > 0 && label < int(reduced_comp.size())) reduced_comp[label] = idx;
                }
                expanded.push_back(move(labels));
            }
        }

        for (const ChainRecord& rec : chains) {
            int ca = (rec.a > 0 && rec.a < int(reduced_comp.size())) ? reduced_comp[rec.a] : -1;
            int cb = (rec.b > 0 && rec.b < int(reduced_comp.size())) ? reduced_comp[rec.b] : -1;
            int cc = (rec.c > 0 && rec.c < int(reduced_comp.size())) ? reduced_comp[rec.c] : -1;
            bool inserted = false;
            if (ca >= 0 && ca == cb && ca == cc) {
                vector<int> candidate = merge_sorted(expanded[ca], rec.deleted_orig);
                int id = 0;
                if (shape_for_labels(original_trees, out_interner, candidate, id)) {
                    expanded[ca].swap(candidate);
                    inserted = true;
                }
            }
            if (!inserted) expanded.push_back(rec.deleted_orig);
        }

        for (const vector<int>& labels : forced_singletons) expanded.push_back(labels);

        vector<pair<int, string>> output;
        for (const vector<int>& labels : expanded) {
            if (labels.empty()) continue;
            int id = 0;
            if (shape_for_labels(original_trees, out_interner, labels, id)) {
                output.push_back({labels.front(), out_interner.to_newick(id)});
            } else {
                for (int label : labels) output.push_back({label, to_string(label)});
            }
        }

        sort(output.begin(), output.end(), [](const auto& a, const auto& b) {
            return a.first < b.first;
        });
        vector<string> lines;
        lines.reserve(output.size());
        for (const auto& p : output) lines.push_back(p.second);
        return lines;
    }
};

struct ReductionPreprocessor {
    struct MTree {
        struct MNode {
            int left = -1, right = -1, parent = -1, label = 0;
            bool live = true;
        };

        int n = 0, root = -1;
        vector<MNode> nodes;
        vector<int> leaf_node;

        bool is_leaf_node(int v) const {
            return v >= 0 && nodes[v].live && nodes[v].label > 0;
        }

        static MTree parse_newick(const string& s, int leaves) {
            MTree t;
            t.n = leaves;
            t.leaf_node.assign(leaves + 1, -1);
            size_t pos = 0;

            function<int()> parse_rec = [&]() -> int {
                while (pos < s.size() && isspace(static_cast<unsigned char>(s[pos]))) ++pos;
                if (s[pos] == '(') {
                    ++pos;
                    int a = parse_rec();
                    while (pos < s.size() && isspace(static_cast<unsigned char>(s[pos]))) ++pos;
                    if (pos < s.size() && s[pos] == ',') ++pos;
                    int b = parse_rec();
                    while (pos < s.size() && isspace(static_cast<unsigned char>(s[pos]))) ++pos;
                    if (pos < s.size() && s[pos] == ')') ++pos;
                    int id = int(t.nodes.size());
                    t.nodes.push_back({a, b, -1, 0, true});
                    t.nodes[a].parent = id;
                    t.nodes[b].parent = id;
                    return id;
                }

                int label = 0;
                while (pos < s.size() && s[pos] >= '0' && s[pos] <= '9') {
                    label = label * 10 + (s[pos] - '0');
                    ++pos;
                }
                int id = int(t.nodes.size());
                t.nodes.push_back({-1, -1, -1, label, true});
                if (1 <= label && label <= leaves) t.leaf_node[label] = id;
                return id;
            };

            t.root = parse_rec();
            if (t.root >= 0) t.nodes[t.root].parent = -1;
            return t;
        }

        int sibling_node(int v) const {
            int p = nodes[v].parent;
            if (p < 0) return -1;
            return nodes[p].left == v ? nodes[p].right : nodes[p].left;
        }

        int part_of_cherry(int taxon) const {
            if (taxon <= 0 || taxon >= int(leaf_node.size())) return 0;
            int v = leaf_node[taxon];
            if (v < 0 || !is_leaf_node(v)) return 0;
            int s = sibling_node(v);
            if (is_leaf_node(s)) return nodes[s].label;
            return 0;
        }

        int number_leaf_children(int v) const {
            if (v < 0 || is_leaf_node(v)) return 0;
            return int(is_leaf_node(nodes[v].left)) + int(is_leaf_node(nodes[v].right));
        }

        int leaf_child_taxon(int v) const {
            if (v < 0 || is_leaf_node(v)) return 0;
            if (is_leaf_node(nodes[v].left)) return nodes[nodes[v].left].label;
            if (is_leaf_node(nodes[v].right)) return nodes[nodes[v].right].label;
            return 0;
        }

        int non_leaf_child(int v) const {
            if (v < 0 || is_leaf_node(v)) return -1;
            if (!is_leaf_node(nodes[v].left)) return nodes[v].left;
            if (!is_leaf_node(nodes[v].right)) return nodes[v].right;
            return -1;
        }

        bool has_leaf_child(int v, int taxon) const {
            if (v < 0 || is_leaf_node(v)) return false;
            return (is_leaf_node(nodes[v].left) && nodes[nodes[v].left].label == taxon) ||
                   (is_leaf_node(nodes[v].right) && nodes[nodes[v].right].label == taxon);
        }

        int delete_taxon(int taxon) {
            int leaf = (taxon > 0 && taxon < int(leaf_node.size())) ? leaf_node[taxon] : -1;
            if (leaf < 0 || !is_leaf_node(leaf)) return 0;
            int p = nodes[leaf].parent;
            if (p < 0) {
                nodes[leaf].live = false;
                leaf_node[taxon] = -1;
                root = -1;
                return 0;
            }
            int sib = sibling_node(leaf);
            int gp = nodes[p].parent;
            if (gp < 0) {
                root = sib;
                nodes[sib].parent = -1;
            } else {
                if (nodes[gp].left == p) nodes[gp].left = sib;
                else nodes[gp].right = sib;
                nodes[sib].parent = gp;
            }
            nodes[leaf].live = false;
            nodes[p].live = false;
            leaf_node[taxon] = -1;
            nodes[leaf].parent = -1;
            nodes[p].left = nodes[p].right = nodes[p].parent = -1;
            return is_leaf_node(sib) ? nodes[sib].label : 0;
        }

        void collect_local_taxa(int taxon, vector<int>& out) const {
            if (taxon <= 0 || taxon >= int(leaf_node.size())) return;
            int v = leaf_node[taxon];
            if (v < 0 || !nodes[v].live) return;
            int at = v;
            for (int up_steps = 0; at >= 0 && up_steps < 8; ++up_steps, at = nodes[at].parent) {
                vector<pair<int, int>> st = {{at, 0}};
                while (!st.empty()) {
                    auto [x, d] = st.back();
                    st.pop_back();
                    if (x < 0 || !nodes[x].live || d > 4) continue;
                    if (is_leaf_node(x)) {
                        out.push_back(nodes[x].label);
                    } else {
                        st.push_back({nodes[x].left, d + 1});
                        st.push_back({nodes[x].right, d + 1});
                    }
                }
            }
        }

        string to_newick(int v, const vector<int>& relabel) const {
            if (is_leaf_node(v)) return to_string(relabel[nodes[v].label]);
            return "(" + to_newick(nodes[v].left, relabel) + "," +
                   to_newick(nodes[v].right, relabel) + ")";
        }
    };

    struct RawChainRecord {
        int a = 0, b = 0, c = 0, d = 0;
    };

    int original_n = 0;
    MTree trees[2];
    vector<int> dsu;
    vector<char> active_taxon;
    vector<vector<int>> taxon_orig;
    vector<RawChainRecord> raw_chains;
    vector<vector<int>> forced_singletons;
    deque<int> queue;
    vector<char> in_queue;
    int subtree_reductions = 0;
    int chain_reductions = 0;
    int three_two_reductions = 0;

    int find_rep(int x) {
        if (x <= 0 || x >= int(dsu.size())) return 0;
        if (dsu[x] == x) return x;
        dsu[x] = find_rep(dsu[x]);
        return dsu[x];
    }

    void enqueue_taxon(int x) {
        if (x <= 0 || x > original_n || !active_taxon[x] || in_queue[x]) return;
        in_queue[x] = 1;
        queue.push_back(x);
    }

    void enqueue_neighborhood(int x) {
        vector<int> local;
        local.reserve(128);
        for (int ti = 0; ti < 2; ++ti) trees[ti].collect_local_taxa(x, local);
        for (int y : local) enqueue_taxon(y);
    }

    static vector<int> merge_orig(const vector<int>& a, const vector<int>& b) {
        vector<int> out;
        out.reserve(a.size() + b.size());
        merge(a.begin(), a.end(), b.begin(), b.end(), back_inserter(out));
        return out;
    }

    bool reduce_common_cherry(int x) {
        if (!active_taxon[x]) return false;
        int s0 = trees[0].part_of_cherry(x);
        int s1 = trees[1].part_of_cherry(x);
        if (s0 <= 0 || s0 != s1 || !active_taxon[s0]) return false;
        int keep = min(x, s0);
        int del = max(x, s0);
        if (trees[0].part_of_cherry(keep) != del || trees[1].part_of_cherry(keep) != del) {
            return false;
        }

        taxon_orig[keep] = merge_orig(taxon_orig[keep], taxon_orig[del]);
        dsu[del] = keep;
        active_taxon[del] = 0;
        int moved0 = trees[0].delete_taxon(del);
        int moved1 = trees[1].delete_taxon(del);
        ++subtree_reductions;

        enqueue_neighborhood(keep);
        enqueue_neighborhood(moved0);
        enqueue_neighborhood(moved1);
        return true;
    }

    bool find_common_four_chain(int x, int chain[4]) const {
        if (!active_taxon[x]) return false;
        int at[2] = {trees[0].leaf_node[x], trees[1].leaf_node[x]};
        if (at[0] < 0 || at[1] < 0) return false;
        at[0] = trees[0].nodes[at[0]].parent;
        at[1] = trees[1].nodes[at[1]].parent;
        if (at[0] < 0 || at[1] < 0) return false;
        if (trees[0].number_leaf_children(at[0]) != 1) return false;
        if (trees[1].number_leaf_children(at[1]) != 1) return false;
        if (trees[0].leaf_child_taxon(at[0]) != x) return false;
        if (trees[1].leaf_child_taxon(at[1]) != x) return false;
        at[0] = trees[0].non_leaf_child(at[0]);
        at[1] = trees[1].non_leaf_child(at[1]);
        if (at[0] < 0 || at[1] < 0) return false;
        if (trees[0].number_leaf_children(at[0]) != 1) return false;
        if (trees[1].number_leaf_children(at[1]) != 1) return false;
        int second = trees[0].leaf_child_taxon(at[0]);
        if (second <= 0 || second != trees[1].leaf_child_taxon(at[1])) return false;

        chain[0] = x;
        chain[1] = second;
        at[0] = trees[0].non_leaf_child(at[0]);
        at[1] = trees[1].non_leaf_child(at[1]);
        if (at[0] < 0 || at[1] < 0) return false;

        int nlc0 = trees[0].number_leaf_children(at[0]);
        int nlc1 = trees[1].number_leaf_children(at[1]);
        if (nlc0 != 1 && nlc1 != 1) return false;

        int third = 0;
        if (nlc0 == 1 && nlc1 == 1) {
            third = trees[0].leaf_child_taxon(at[0]);
            if (third <= 0 || third != trees[1].leaf_child_taxon(at[1])) return false;
            at[0] = trees[0].non_leaf_child(at[0]);
            at[1] = trees[1].non_leaf_child(at[1]);
        } else if (nlc0 == 1 && nlc1 == 2) {
            third = trees[0].leaf_child_taxon(at[0]);
            if (!trees[1].has_leaf_child(at[1], third)) return false;
            at[0] = trees[0].non_leaf_child(at[0]);
        } else if (nlc0 == 2 && nlc1 == 1) {
            third = trees[1].leaf_child_taxon(at[1]);
            if (!trees[0].has_leaf_child(at[0], third)) return false;
            at[1] = trees[1].non_leaf_child(at[1]);
        } else {
            return false;
        }

        if (third <= 0 || at[0] < 0 || at[1] < 0) return false;
        chain[2] = third;
        for (int child : {trees[0].nodes[at[0]].left, trees[0].nodes[at[0]].right}) {
            if (!trees[0].is_leaf_node(child)) continue;
            int y = trees[0].nodes[child].label;
            if (active_taxon[y] && trees[1].has_leaf_child(at[1], y)) {
                chain[3] = y;
                return true;
            }
        }
        return false;
    }

    bool reduce_common_chain(int x) {
        int chain[4] = {0, 0, 0, 0};
        if (!find_common_four_chain(x, chain)) return false;
        int del = chain[3];
        raw_chains.push_back({chain[0], chain[1], chain[2], del});
        active_taxon[del] = 0;
        int moved0 = trees[0].delete_taxon(del);
        int moved1 = trees[1].delete_taxon(del);
        ++chain_reductions;

        for (int i = 0; i < 3; ++i) enqueue_neighborhood(chain[i]);
        enqueue_neighborhood(moved0);
        enqueue_neighborhood(moved1);
        return true;
    }

    bool reduce_three_two(int p) {
        if (!active_taxon[p]) return false;
        int sibling0 = trees[0].part_of_cherry(p);
        int sibling1 = trees[1].part_of_cherry(p);
        if (sibling0 <= 0 || sibling1 <= 0 || sibling0 == sibling1) return false;

        int q = sibling0;
        int q_node_t1 = trees[1].leaf_node[q];
        int r = sibling1;
        int r_node_t1 = trees[1].leaf_node[r];
        if (q_node_t1 >= 0 && r_node_t1 >= 0) {
            int rp = trees[1].nodes[r_node_t1].parent;
            int rgp = (rp >= 0) ? trees[1].nodes[rp].parent : -1;
            int qp = trees[1].nodes[q_node_t1].parent;
            if (rgp >= 0 && rgp == qp && active_taxon[r]) {
                forced_singletons.push_back(taxon_orig[r]);
                active_taxon[r] = 0;
                int moved0 = trees[0].delete_taxon(r);
                int moved1 = trees[1].delete_taxon(r);
                ++three_two_reductions;
                enqueue_neighborhood(p);
                enqueue_neighborhood(q);
                enqueue_neighborhood(moved0);
                enqueue_neighborhood(moved1);
                return true;
            }
        }

        q = sibling1;
        int q_node_t0 = trees[0].leaf_node[q];
        r = sibling0;
        int r_node_t0 = trees[0].leaf_node[r];
        if (q_node_t0 >= 0 && r_node_t0 >= 0) {
            int rp = trees[0].nodes[r_node_t0].parent;
            int rgp = (rp >= 0) ? trees[0].nodes[rp].parent : -1;
            int qp = trees[0].nodes[q_node_t0].parent;
            if (rgp >= 0 && rgp == qp && active_taxon[r]) {
                forced_singletons.push_back(taxon_orig[r]);
                active_taxon[r] = 0;
                int moved0 = trees[0].delete_taxon(r);
                int moved1 = trees[1].delete_taxon(r);
                ++three_two_reductions;
                enqueue_neighborhood(p);
                enqueue_neighborhood(q);
                enqueue_neighborhood(moved0);
                enqueue_neighborhood(moved1);
                return true;
            }
        }

        return false;
    }

    bool try_reduce_at(int x, bool use_chain, bool use_three_two) {
        if (!active_taxon[x]) return false;
        if (reduce_common_cherry(x)) return true;
        if (use_chain && reduce_common_chain(x)) return true;
        if (use_three_two && reduce_three_two(x)) return true;
        return false;
    }

    bool run(vector<string>& newicks, int& n, bool use_chain, bool use_three_two,
             ReductionExpansion& expansion) {
        if (newicks.size() != 2 || n <= 0) return false;
        original_n = n;
        trees[0] = MTree::parse_newick(newicks[0], original_n);
        trees[1] = MTree::parse_newick(newicks[1], original_n);
        dsu.resize(original_n + 1);
        iota(dsu.begin(), dsu.end(), 0);
        active_taxon.assign(original_n + 1, 1);
        active_taxon[0] = 0;
        taxon_orig.assign(original_n + 1, {});
        for (int label = 1; label <= original_n; ++label) taxon_orig[label] = {label};
        in_queue.assign(original_n + 1, 0);
        for (int label = 1; label <= original_n; ++label) enqueue_taxon(label);

        while (true) {
            while (!queue.empty()) {
                int x = queue.front();
                queue.pop_front();
                in_queue[x] = 0;
                try_reduce_at(x, use_chain, use_three_two);
            }

            bool missed = false;
            for (int x = 1; x <= original_n; ++x) {
                if (active_taxon[x] && try_reduce_at(x, use_chain, use_three_two)) {
                    missed = true;
                    break;
                }
            }
            if (!missed) break;
        }

        vector<int> old_to_reduced(original_n + 1, 0);
        vector<int> active_old;
        for (int label = 1; label <= original_n; ++label) {
            if (active_taxon[label]) {
                old_to_reduced[label] = int(active_old.size()) + 1;
                active_old.push_back(label);
            }
        }
        if (active_old.empty()) return false;

        vector<int> relabel(original_n + 1, 0);
        vector<vector<int>> reduced_orig(active_old.size() + 1);
        for (int old : active_old) {
            int r = old_to_reduced[old];
            relabel[old] = r;
            reduced_orig[r] = taxon_orig[old];
        }

        vector<ReductionExpansion::ChainRecord> final_chains;
        final_chains.reserve(raw_chains.size());
        for (const RawChainRecord& rec : raw_chains) {
            int ra = old_to_reduced[find_rep(rec.a)];
            int rb = old_to_reduced[find_rep(rec.b)];
            int rc = old_to_reduced[find_rep(rec.c)];
            final_chains.push_back({ra, rb, rc, taxon_orig[rec.d]});
        }

        expansion.active = (subtree_reductions + chain_reductions + three_two_reductions > 0);
        expansion.original_n = original_n;
        expansion.original_newicks = newicks;
        expansion.reduced_orig = move(reduced_orig);
        expansion.chains = move(final_chains);
        expansion.forced_singletons = forced_singletons;

        if (!expansion.active) return false;

        newicks[0] = trees[0].to_newick(trees[0].root, relabel) + ";";
        newicks[1] = trees[1].to_newick(trees[1].root, relabel) + ";";
        n = int(active_old.size());
        VERBOSE_CERR << "# reductions subtree " << subtree_reductions
             << " chain " << chain_reductions
             << " three_two " << three_two_reductions
             << " reduced_leaves " << n << "/" << original_n << "\n";
        return true;
    }
};

struct Candidate {
    int node = -1;
    int size = 0;
};

struct GreedyMergeSolver {
    int n = 0;
    Tree trees[2];
    Interner interner;
    Timer& timer;
    uint64_t rng = 0x123456789abcdefULL;

    explicit GreedyMergeSolver(Timer& t) : timer(t) {}

    uint64_t next_rand() {
        rng ^= rng << 7;
        rng ^= rng >> 9;
        return rng;
    }

    static vector<int> merge_sorted_labels(const vector<int>& a, const vector<int>& b) {
        vector<int> out;
        out.reserve(a.size() + b.size());
        merge(a.begin(), a.end(), b.begin(), b.end(), back_inserter(out));
        return out;
    }

    vector<int> merge_tin_labels(const vector<int>& a, const vector<int>& b, int ti) const {
        vector<int> out;
        out.reserve(a.size() + b.size());
        size_t i = 0, j = 0;
        while (i < a.size() || j < b.size()) {
            if (j == b.size() ||
                (i < a.size() && trees[ti].tin[trees[ti].leaf_node[a[i]]] <
                                    trees[ti].tin[trees[ti].leaf_node[b[j]]])) {
                out.push_back(a[i++]);
            } else {
                out.push_back(b[j++]);
            }
        }
        return out;
    }

    vector<Candidate> build_candidates(int base_idx) {
        int other_idx = 1 - base_idx;
        const Tree& base = trees[base_idx];
        const Tree& other = trees[other_idx];
        vector<Candidate> candidates;
        vector<vector<int>> tmp(base.nodes.size());

        for (int v = 0; v < int(base.nodes.size()) && !timer.expired(); ++v) {
            if (base.is_leaf(v)) {
                tmp[v].push_back(base.nodes[v].label);
                continue;
            }

            int l = base.nodes[v].left, r = base.nodes[v].right;
            vector<int> merged;
            merged.reserve(tmp[l].size() + tmp[r].size());
            size_t i = 0, j = 0;
            while (i < tmp[l].size() || j < tmp[r].size()) {
                if (j == tmp[r].size() ||
                    (i < tmp[l].size() && other.tin[other.leaf_node[tmp[l][i]]] <
                                             other.tin[other.leaf_node[tmp[r][j]]])) {
                    merged.push_back(tmp[l][i++]);
                } else {
                    merged.push_back(tmp[r][j++]);
                }
            }
            tmp[v].swap(merged);
            vector<int>().swap(tmp[l]);
            vector<int>().swap(tmp[r]);

            if (base.leaf_count[v] >= 2) {
                int other_id = other.analyze_sorted_labels(tmp[v], interner, false).id;
                if (other_id == base.subtree_id[v]) candidates.push_back({v, base.leaf_count[v]});
            }
        }

        sort(candidates.begin(), candidates.end(), [](const Candidate& a, const Candidate& b) {
            if (a.size != b.size) return a.size > b.size;
            return a.node < b.node;
        });
        return candidates;
    }

    static bool can_use_edges(const vector<int>& edges, const vector<int>& used) {
        for (int e : edges) {
            if (used[e]) return false;
        }
        return true;
    }

    vector<Component> greedy_forest(int base_idx) {
        vector<Candidate> candidates = build_candidates(base_idx);
        vector<Component> comps;
        vector<int> edge_used[2] = {
            vector<int>(trees[0].nodes.size(), 0),
            vector<int>(trees[1].nodes.size(), 0)
        };
        Fenwick assigned(trees[base_idx].n);
        vector<char> assigned_leaf(n + 1, 0);

        for (const Candidate& cand : candidates) {
            if (timer.expired()) break;
            const Tree& base = trees[base_idx];
            if (assigned.sum_range(base.leaf_l[cand.node], base.leaf_r[cand.node]) != 0) continue;

            vector<int> labels = base.collect_leaves(cand.node);
            vector<int> tin_labels[2] = {
                trees[0].labels_by_tin(labels),
                trees[1].labels_by_tin(labels)
            };
            Tree::Analysis a0 = trees[0].analyze_sorted_labels(tin_labels[0], interner, true);
            Tree::Analysis a1 = trees[1].analyze_sorted_labels(tin_labels[1], interner, true);
            if (a0.id != a1.id) continue;
            if (!can_use_edges(a0.edges, edge_used[0]) || !can_use_edges(a1.edges, edge_used[1])) continue;

            Component comp;
            comp.labels = move(labels);
            comp.tin_labels[0] = move(tin_labels[0]);
            comp.tin_labels[1] = move(tin_labels[1]);
            comp.edges[0] = move(a0.edges);
            comp.edges[1] = move(a1.edges);
            comp.id = a0.id;
            comps.push_back(move(comp));

            for (int label : comps.back().labels) {
                assigned_leaf[label] = 1;
                assigned.add(trees[base_idx].leaf_rank[label], 1);
            }
            for (int ti = 0; ti < 2; ++ti) {
                for (int e : comps.back().edges[ti]) edge_used[ti][e] = 1;
            }
        }

        for (int label = 1; label <= n; ++label) {
            if (assigned_leaf[label]) continue;
            Component comp;
            comp.labels = {label};
            comp.tin_labels[0] = {label};
            comp.tin_labels[1] = {label};
            comp.id = label;
            comps.push_back(move(comp));
        }
        return comps;
    }

    vector<Component> singleton_forest() const {
        vector<Component> comps;
        comps.reserve(n);
        for (int label = 1; label <= n; ++label) {
            Component comp;
            comp.labels = {label};
            comp.tin_labels[0] = {label};
            comp.tin_labels[1] = {label};
            comp.id = label;
            comps.push_back(move(comp));
        }
        return comps;
    }

    struct Forest {
        vector<Component> comps;
        vector<int> edge_used[2];
        vector<int> edge_mark[2];
        vector<int> label_comp;
        int active_count = 0;
        int token = 1;
    };

    Forest make_forest(vector<Component> comps) {
        Forest f;
        f.comps = move(comps);
        f.edge_used[0].assign(trees[0].nodes.size(), 0);
        f.edge_used[1].assign(trees[1].nodes.size(), 0);
        f.edge_mark[0].assign(trees[0].nodes.size(), 0);
        f.edge_mark[1].assign(trees[1].nodes.size(), 0);
        f.label_comp.assign(n + 1, -1);

        for (int i = 0; i < int(f.comps.size()); ++i) {
            if (!f.comps[i].active) continue;
            ++f.active_count;
            for (int label : f.comps[i].labels) f.label_comp[label] = i;
            for (int ti = 0; ti < 2; ++ti) {
                for (int e : f.comps[i].edges[ti]) f.edge_used[ti][e] = 1;
            }
        }
        return f;
    }

    bool component_from_labels(const vector<int>& labels, Component& comp) {
        if (labels.empty()) return false;
        comp = Component();
        comp.labels = labels;
        comp.tin_labels[0] = trees[0].labels_by_tin(labels);
        comp.tin_labels[1] = trees[1].labels_by_tin(labels);
        Tree::Analysis a0 = trees[0].analyze_sorted_labels(comp.tin_labels[0], interner, true);
        Tree::Analysis a1 = trees[1].analyze_sorted_labels(comp.tin_labels[1], interner, true);
        if (a0.id != a1.id) return false;
        comp.id = a0.id;
        comp.edges[0] = move(a0.edges);
        comp.edges[1] = move(a1.edges);
        comp.active = true;
        return true;
    }

    bool try_merge(Forest& f, int ca, int cb) {
        if (ca < 0 || cb < 0 || ca == cb) return false;
        if (ca >= int(f.comps.size()) || cb >= int(f.comps.size())) return false;
        if (!f.comps[ca].active || !f.comps[cb].active) return false;

        Component merged;
        merged.labels = merge_sorted_labels(f.comps[ca].labels, f.comps[cb].labels);
        for (int ti = 0; ti < 2; ++ti) {
            merged.tin_labels[ti] = merge_tin_labels(f.comps[ca].tin_labels[ti],
                                                     f.comps[cb].tin_labels[ti], ti);
        }

        Tree::Analysis a0 = trees[0].analyze_sorted_labels(merged.tin_labels[0], interner, true);
        Tree::Analysis a1 = trees[1].analyze_sorted_labels(merged.tin_labels[1], interner, true);
        if (a0.id != a1.id) return false;
        merged.id = a0.id;
        merged.edges[0] = move(a0.edges);
        merged.edges[1] = move(a1.edges);

        ++f.token;
        if (f.token == 0x3fffffff) {
            fill(f.edge_mark[0].begin(), f.edge_mark[0].end(), 0);
            fill(f.edge_mark[1].begin(), f.edge_mark[1].end(), 0);
            f.token = 1;
        }
        for (int ti = 0; ti < 2; ++ti) {
            for (int e : f.comps[ca].edges[ti]) f.edge_mark[ti][e] = f.token;
            for (int e : f.comps[cb].edges[ti]) f.edge_mark[ti][e] = f.token;
            for (int e : merged.edges[ti]) {
                if (f.edge_used[ti][e] && f.edge_mark[ti][e] != f.token) return false;
            }
        }

        for (int ti = 0; ti < 2; ++ti) {
            for (int e : f.comps[ca].edges[ti]) f.edge_used[ti][e] = 0;
            for (int e : f.comps[cb].edges[ti]) f.edge_used[ti][e] = 0;
            for (int e : merged.edges[ti]) f.edge_used[ti][e] = 1;
        }

        int nid = int(f.comps.size());
        f.comps[ca].active = false;
        f.comps[cb].active = false;
        for (int label : merged.labels) f.label_comp[label] = nid;
        f.comps.push_back(move(merged));
        --f.active_count;
        return true;
    }

    vector<pair<int, int>> build_merge_candidates(const Forest& f) {
        vector<pair<int, int>> pairs;
        unordered_set<uint64_t> seen;
        seen.reserve(8 * n + 1024);

        auto add_pair = [&](int a, int b) {
            if (a < 0 || b < 0 || a == b) return;
            if (!f.comps[a].active || !f.comps[b].active) return;
            int x = min(a, b), y = max(a, b);
            uint64_t key = (uint64_t(uint32_t(x)) << 32) | uint32_t(y);
            if (seen.insert(key).second) pairs.push_back({x, y});
        };

        for (int ti = 0; ti < 2; ++ti) {
            int prev = -1;
            for (int label : trees[ti].leaf_order) {
                int cur = f.label_comp[label];
                if (cur != prev) {
                    add_pair(prev, cur);
                    prev = cur;
                }
            }
        }

        vector<int> active;
        active.reserve(f.active_count);
        for (int i = 0; i < int(f.comps.size()); ++i) {
            if (f.comps[i].active) active.push_back(i);
        }
        if (active.size() > 1) {
            long long exhaustive_pairs = 1LL * active.size() * (active.size() - 1) / 2;
            if (exhaustive_pairs <= 250000) {
                for (size_t i = 0; i < active.size(); ++i) {
                    for (size_t j = i + 1; j < active.size(); ++j) add_pair(active[i], active[j]);
                }
            }

            int samples = min<int>(20000 + int(timer.limit_seconds * 500.0), 180000);
            for (int s = 0; s < samples; ++s) {
                int a = active[next_rand() % active.size()];
                int b = active[next_rand() % active.size()];
                add_pair(a, b);
            }
        }

        sort(pairs.begin(), pairs.end(), [&](const auto& p, const auto& q) {
            int sp = int(f.comps[p.first].labels.size() + f.comps[p.second].labels.size());
            int sq = int(f.comps[q.first].labels.size() + f.comps[q.second].labels.size());
            if (sp != sq) return sp > sq;
            return p < q;
        });
        return pairs;
    }

    void improve(Forest& f) {
        for (int pass = 1; !timer.expired(); ++pass) {
            vector<pair<int, int>> candidates = build_merge_candidates(f);
            int merges = 0;
            for (auto [a, b] : candidates) {
                if (timer.expired()) break;
                if (try_merge(f, a, b)) ++merges;
            }
            VERBOSE_CERR << "# pass " << pass << " candidates " << candidates.size()
                 << " merges " << merges << " components " << f.active_count << "\n";
            if (merges == 0 && (f.active_count < 2 || pass >= 20 || timer.limit_seconds < 10.0)) break;
        }
    }

    bool try_split_merge_once(Forest& f, int comp_idx, int label) {
        if (comp_idx < 0 || comp_idx >= int(f.comps.size())) return false;
        const Component& source = f.comps[comp_idx];
        if (!source.active || source.labels.size() <= 1) return false;

        vector<int> rest;
        rest.reserve(source.labels.size() - 1);
        bool found = false;
        for (int x : source.labels) {
            if (x == label) found = true;
            else rest.push_back(x);
        }
        if (!found || rest.empty()) return false;

        Component rest_comp;
        if (!component_from_labels(rest, rest_comp)) return false;

        vector<Component> trial_comps;
        trial_comps.reserve(f.active_count + 1);
        for (int i = 0; i < int(f.comps.size()); ++i) {
            if (!f.comps[i].active) continue;
            if (i == comp_idx) {
                trial_comps.push_back(move(rest_comp));
                Component single;
                single.labels = {label};
                single.tin_labels[0] = {label};
                single.tin_labels[1] = {label};
                single.id = label;
                single.active = true;
                trial_comps.push_back(move(single));
            } else {
                trial_comps.push_back(f.comps[i]);
            }
        }

        Forest trial = make_forest(move(trial_comps));
        if (trial.active_count != f.active_count + 1) return false;
        improve(trial);
        if (!timer.expired() && trial.active_count < f.active_count) {
            f = move(trial);
            return true;
        }
        return false;
    }

    int split_merge_polish(Forest& f) {
        int improvements = 0;
        bool changed = true;
        while (changed && !timer.expired() && f.active_count > 1) {
            changed = false;
            vector<int> active;
            active.reserve(f.active_count);
            for (int i = 0; i < int(f.comps.size()); ++i) {
                if (f.comps[i].active && f.comps[i].labels.size() > 1) active.push_back(i);
            }

            for (int ci : active) {
                if (timer.expired()) break;
                if (ci >= int(f.comps.size()) || !f.comps[ci].active || f.comps[ci].labels.size() <= 1) continue;
                vector<int> labels = f.comps[ci].labels;
                for (int label : labels) {
                    if (timer.expired()) break;
                    if (try_split_merge_once(f, ci, label)) {
                        ++improvements;
                        changed = true;
                        break;
                    }
                }
                if (changed) break;
            }
        }
        return improvements;
    }

    vector<Component> active_components(const Forest& f) const {
        vector<Component> out;
        out.reserve(f.active_count);
        for (const Component& c : f.comps) {
            if (c.active) out.push_back(c);
        }
        sort(out.begin(), out.end(), [](const Component& a, const Component& b) {
            return a.labels.front() < b.labels.front();
        });
        return out;
    }

    vector<Component> solve() {
        vector<Component> best;
        for (int base = 0; base < 2 && !timer.expired(); ++base) {
            VERBOSE_CERR << "# building greedy forest from tree " << (base + 1) << "\n";
            vector<Component> initial = greedy_forest(base);
            Forest f = make_forest(move(initial));
            VERBOSE_CERR << "# initial components " << f.active_count << "\n";
            improve(f);
            vector<Component> current = active_components(f);
            VERBOSE_CERR << "# final components from tree " << (base + 1) << ": " << current.size() << "\n";
            if (best.empty() || current.size() < best.size()) best = move(current);
        }

        if (!timer.expired() && (n <= 5000 || timer.limit_seconds >= 10.0)) {
            VERBOSE_CERR << "# building singleton-start forest\n";
            Forest f = make_forest(singleton_forest());
            improve(f);
            vector<Component> current = active_components(f);
            VERBOSE_CERR << "# final components from singleton start: " << current.size() << "\n";
            if (best.empty() || current.size() < best.size()) best = move(current);
        }

        if (best.empty()) {
            for (int label = 1; label <= n; ++label) {
                Component c;
                c.labels = {label};
                c.id = label;
                best.push_back(move(c));
            }
        }
        return best;
    }
};

static double read_time_limit(int argc, char** argv) {
    double limit = 295.0;
    if (const char* env = getenv("STRIDE_TIMEOUT")) {
        double v = atof(env);
        if (v > 0.1) limit = max(0.1, v - 0.5);
    }
    for (int i = 1; i + 1 < argc; ++i) {
        string arg = argv[i];
        if (arg == "--time") {
            double v = atof(argv[i + 1]);
            if (v > 0.1) limit = v;
        }
    }
    return limit;
}

struct AnnealEval {
    bool feasible = false;
    int components = 0;
    int penalty = 0;
    double energy = 0.0;
    vector<Component> comps;
};

struct AnnealMove {
    vector<pair<int, unsigned char>> changes;
};

struct AnnealSolver {
    int n = 0;
    vector<string> newicks;
    Tree trees[2];
    Interner interner;
    Timer& timer;
    uint64_t rng;
    ReductionExpansion reductions;
    vector<int> nonroot_edges;
    vector<int> t1_sorted_edges;  // nonroot_edges sorted by T1 subtree min-rank
    vector<int> t1_edge_pos;      // t1_edge_pos[node] = position in t1_sorted_edges
    vector<int> t1_min_rank_vec;  // t1_min_rank_vec[node] = min T1 leaf rank in T0 subtree
    vector<int> t1_max_rank_vec;  // t1_max_rank_vec[node] = max T1 leaf rank in T0 subtree
    vector<int> t0_sorted_edges;      // nonroot_edges sorted by T0 subtree min-rank
    vector<int> t0_edge_pos;          // t0_edge_pos[node] = position in t0_sorted_edges
    vector<int> t0_min_rank_vec;      // t0_min_rank_vec[node] = min T0 leaf rank in T0 subtree
    vector<int> t0_max_rank_vec;      // t0_max_rank_vec[node] = max T0 leaf rank in T0 subtree
    int pair_window = 10;
    vector<int> eval_comp_root;
    vector<int> eval_sub_shape, eval_sub_count, eval_comp_shape, eval_comp_total;
    vector<int> eval_leaf_comp, eval_active_roots;
    vector<int> eval_open_comp, eval_open_count, eval_open_shape, eval_t2_shape;
    vector<uint64_t> fast_sub, fast_comp, fast_open, fast_t2;
    vector<int> fast_open_count, fast_sub_count;

    explicit AnnealSolver(Timer& t, uint64_t seed) : timer(t), rng(seed) {}

    uint64_t next_rand() {
        rng ^= rng << 7;
        rng ^= rng >> 9;
        return rng;
    }

    int rnd_int(int bound) {
        return int(next_rand() % uint64_t(bound));
    }

    double rnd01() {
        return double(next_rand() >> 11) * (1.0 / 9007199254740992.0);
    }

    static int infer_leaf_count(const vector<string>& input_newicks) {
        int inferred = 0;
        for (const string& s : input_newicks) {
            int cur = 0;
            for (char ch : s) {
                if ('0' <= ch && ch <= '9') {
                    cur = 10 * cur + (ch - '0');
                } else {
                    inferred = max(inferred, cur);
                    cur = 0;
                }
            }
            inferred = max(inferred, cur);
        }
        return inferred;
    }

    void load_instance(vector<string> input_newicks, int input_n) {
        n = input_n > 0 ? input_n : infer_leaf_count(input_newicks);
        newicks = input_newicks;
        reductions = ReductionExpansion();
        nonroot_edges.clear();
        interner.reset(n);

        if (newicks.size() == 2) {
            bool do_swap = SWAP_TREES != 0;
            if (do_swap) swap(newicks[0], newicks[1]);
            int reduction_before_n = n;
            size_t reduction_before_chars = 0;
            for (const string& s : newicks) reduction_before_chars += s.size();
            auto reduction_start = chrono::steady_clock::now();
            bool reduction_changed = false;
            ReductionPreprocessor pre;
            reduction_changed = pre.run(newicks, n, REDUCE_CHAIN, REDUCE_THREE_TWO, reductions);
            double reduction_seconds = chrono::duration<double>(
                chrono::steady_clock::now() - reduction_start).count();
            size_t reduction_after_chars = 0;
            for (const string& s : newicks) reduction_after_chars += s.size();
            VERBOSE_CERR << "# reductions timing solver_id " << reinterpret_cast<uintptr_t>(this)
                 << " changed " << (reduction_changed ? 1 : 0)
                 << " time_sec " << reduction_seconds
                 << " leaves_before " << reduction_before_n
                 << " leaves_after " << n
                 << " nodes_before " << max(0, 2 * reduction_before_n - 1)
                 << " nodes_after " << max(0, 2 * n - 1)
                 << " newick_chars_before " << reduction_before_chars
                 << " newick_chars_after " << reduction_after_chars
                 << " chain " << REDUCE_CHAIN
                 << " three_two " << REDUCE_THREE_TWO << "\n";
            trees[0] = Tree::parse_newick(newicks[0], n);
            trees[1] = Tree::parse_newick(newicks[1], n);
            interner.reset(n);
            trees[0].preprocess(interner);
            trees[1].preprocess(interner);
            for (int v = 0; v < int(trees[0].nodes.size()); ++v) {
                if (v == trees[0].root) continue;
                nonroot_edges.push_back(v);
            }

            int num_t0 = int(trees[0].nodes.size());
            t1_min_rank_vec.assign(num_t0, n + 1);
            t1_max_rank_vec.assign(num_t0, -1);
            {
                vector<int> po(num_t0);
                iota(po.begin(), po.end(), 0);
                sort(po.begin(), po.end(), [&](int a, int b) {
                    return trees[0].tout[a] < trees[0].tout[b];
                });
                for (int v : po) {
                    if (trees[0].is_leaf(v)) {
                        int r = trees[1].leaf_rank[trees[0].nodes[v].label];
                        t1_min_rank_vec[v] = r;
                        t1_max_rank_vec[v] = r;
                    } else {
                        int l = trees[0].nodes[v].left;
                        int r = trees[0].nodes[v].right;
                        t1_min_rank_vec[v] = min(t1_min_rank_vec[l], t1_min_rank_vec[r]);
                        t1_max_rank_vec[v] = max(t1_max_rank_vec[l], t1_max_rank_vec[r]);
                    }
                }
            }

            t1_sorted_edges = nonroot_edges;
            sort(t1_sorted_edges.begin(), t1_sorted_edges.end(), [&](int a, int b) {
                return t1_min_rank_vec[a] < t1_min_rank_vec[b];
            });
            t1_edge_pos.assign(num_t0, -1);
            for (int i = 0; i < int(t1_sorted_edges.size()); ++i) {
                t1_edge_pos[t1_sorted_edges[i]] = i;
            }

            pair_window = max(10, int(sqrt(double(nonroot_edges.size()))));

            t0_min_rank_vec.assign(num_t0, n + 1);
            t0_max_rank_vec.assign(num_t0, -1);
            {
                vector<int> po(num_t0);
                iota(po.begin(), po.end(), 0);
                sort(po.begin(), po.end(), [&](int a, int b) {
                    return trees[0].tout[a] < trees[0].tout[b];
                });
                for (int v : po) {
                    if (trees[0].is_leaf(v)) {
                        int r = trees[0].leaf_rank[trees[0].nodes[v].label];
                        t0_min_rank_vec[v] = r;
                        t0_max_rank_vec[v] = r;
                    } else {
                        int l = trees[0].nodes[v].left;
                        int r = trees[0].nodes[v].right;
                        t0_min_rank_vec[v] = min(t0_min_rank_vec[l], t0_min_rank_vec[r]);
                        t0_max_rank_vec[v] = max(t0_max_rank_vec[l], t0_max_rank_vec[r]);
                    }
                }
            }

            t0_sorted_edges = nonroot_edges;
            sort(t0_sorted_edges.begin(), t0_sorted_edges.end(), [&](int a, int b) {
                return t0_min_rank_vec[a] < t0_min_rank_vec[b];
            });
            t0_edge_pos.assign(num_t0, -1);
            for (int i = 0; i < int(t0_sorted_edges.size()); ++i) {
                t0_edge_pos[t0_sorted_edges[i]] = i;
            }
        }
    }

    vector<unsigned char> singleton_cuts() const {
        vector<unsigned char> cut(trees[0].nodes.size(), 0);
        for (int label = 1; label <= n; ++label) {
            int v = trees[0].leaf_node[label];
            if (v != trees[0].root) cut[v] = 1;
        }
        return cut;
    }

    void collect_descendants(int node, vector<int>& out) const {
        vector<int> st = {node};
        while (!st.empty()) {
            int v = st.back();
            st.pop_back();
            out.push_back(v);
            if (!trees[0].is_leaf(v)) {
                st.push_back(trees[0].nodes[v].left);
                st.push_back(trees[0].nodes[v].right);
            }
        }
    }

    vector<Candidate> build_common_clade_candidates() {
        const Tree& base = trees[0];
        const Tree& other = trees[1];
        vector<Candidate> candidates;
        vector<vector<int>> tmp(base.nodes.size());

        for (int v = 0; v < int(base.nodes.size()) && !timer.expired(); ++v) {
            if (base.is_leaf(v)) {
                tmp[v].push_back(base.nodes[v].label);
                continue;
            }
            int l = base.nodes[v].left, r = base.nodes[v].right;
            vector<int> merged;
            merged.reserve(tmp[l].size() + tmp[r].size());
            size_t i = 0, j = 0;
            while (i < tmp[l].size() || j < tmp[r].size()) {
                if (j == tmp[r].size() ||
                    (i < tmp[l].size() && other.tin[other.leaf_node[tmp[l][i]]] <
                                             other.tin[other.leaf_node[tmp[r][j]]])) {
                    merged.push_back(tmp[l][i++]);
                } else {
                    merged.push_back(tmp[r][j++]);
                }
            }
            tmp[v].swap(merged);
            vector<int>().swap(tmp[l]);
            vector<int>().swap(tmp[r]);

            if (base.leaf_count[v] >= 2) {
                int other_id = other.analyze_sorted_labels(tmp[v], interner, false).id;
                if (other_id == base.subtree_id[v]) candidates.push_back({v, base.leaf_count[v]});
            }
        }

        sort(candidates.begin(), candidates.end(), [](const Candidate& a, const Candidate& b) {
            if (a.size != b.size) return a.size > b.size;
            return a.node < b.node;
        });
        return candidates;
    }

    struct ClusterSplit {
        bool found = false;
        int node = -1;
        vector<int> inside;
        vector<int> outside;
    };

    struct MultiClusterSplit {
        bool found = false;
        vector<int> nodes;
        vector<vector<int>> sides;
    };

    static uint64_t interval_key(int l, int r) {
        return (uint64_t(uint32_t(l)) << 32) | uint32_t(r);
    }

    ClusterSplit find_cluster_split() const {
        ClusterSplit split;
        if (newicks.size() != 2 || n < CLUSTER_MIN_N) return split;

        int min_side = max(CLUSTER_MIN_SIDE,
                           int(ceil(CLUSTER_MIN_FRAC * double(n))));
        if (min_side <= 0) min_side = 1;
        if (2 * min_side > n) return split;

        unordered_set<uint64_t> t1_intervals;
        t1_intervals.reserve(2 * trees[1].nodes.size() + 1);
        for (int v = 0; v < int(trees[1].nodes.size()); ++v) {
            int cnt = trees[1].leaf_count[v];
            if (cnt > 0 && cnt < n) {
                t1_intervals.insert(interval_key(trees[1].leaf_l[v], trees[1].leaf_r[v]));
            }
        }

        const Tree& t0 = trees[0];
        const Tree& t1 = trees[1];
        vector<int> min_rank(t0.nodes.size(), n + 1), max_rank(t0.nodes.size(), 0);
        int best_node = -1;
        int best_balance = n + 1;
        int best_small_side = -1;

        for (int v = 0; v < int(t0.nodes.size()); ++v) {
            if (t0.is_leaf(v)) {
                int label = t0.nodes[v].label;
                int r = t1.leaf_rank[label];
                min_rank[v] = max_rank[v] = r;
                continue;
            }

            int l = t0.nodes[v].left;
            int r = t0.nodes[v].right;
            min_rank[v] = min(min_rank[l], min_rank[r]);
            max_rank[v] = max(max_rank[l], max_rank[r]);

            int size = t0.leaf_count[v];
            if (v == t0.root || size <= 1 || size >= n) continue;
            int other = n - size;
            int small_side = min(size, other);
            if (small_side < min_side) continue;
            if (max_rank[v] - min_rank[v] + 1 != size) continue;
            if (!t1_intervals.count(interval_key(min_rank[v], max_rank[v]))) continue;

            int balance = abs(n - 2 * size);
            if (balance < best_balance ||
                (balance == best_balance && small_side > best_small_side)) {
                best_balance = balance;
                best_small_side = small_side;
                best_node = v;
            }
        }

        if (best_node < 0) return split;
        split.found = true;
        split.node = best_node;
        split.inside = t0.collect_leaves(best_node);
        vector<char> mark(n + 1, 0);
        for (int label : split.inside) mark[label] = 1;
        split.outside.reserve(n - split.inside.size());
        for (int label = 1; label <= n; ++label) {
            if (!mark[label]) split.outside.push_back(label);
        }
        return split;
    }

    MultiClusterSplit find_multi_cluster_split(int max_cuts) const {
        MultiClusterSplit split;
        if (newicks.size() != 2 || n < CLUSTER_MIN_N || max_cuts <= 0) return split;

        int min_side = max(CLUSTER_MIN_SIDE,
                           int(ceil(CLUSTER_MIN_FRAC * double(n))));
        if (min_side <= 0) min_side = 1;
        if (2 * min_side > n) return split;

        int max_feasible_cuts = max(0, n / min_side - 1);
        max_cuts = min(max_cuts, max_feasible_cuts);
        if (max_cuts <= 0) return split;

        double target_block = double(n) / double(max_cuts + 1);
        int min_block = max(min_side, int(floor(target_block * 0.5)));
        int max_block = max(min_block, int(ceil(target_block * 1.5)));

        unordered_set<uint64_t> t1_intervals;
        t1_intervals.reserve(2 * trees[1].nodes.size() + 1);
        for (int v = 0; v < int(trees[1].nodes.size()); ++v) {
            int cnt = trees[1].leaf_count[v];
            if (cnt > 0 && cnt < n) {
                t1_intervals.insert(interval_key(trees[1].leaf_l[v], trees[1].leaf_r[v]));
            }
        }

        struct Candidate {
            int node = -1;
            int size = 0;
            int score = 0;
        };

        vector<Candidate> candidates;
        const Tree& t0 = trees[0];
        const Tree& t1 = trees[1];
        vector<int> min_rank(t0.nodes.size(), n + 1), max_rank(t0.nodes.size(), 0);
        for (int v = 0; v < int(t0.nodes.size()); ++v) {
            if (t0.is_leaf(v)) {
                int label = t0.nodes[v].label;
                int r = t1.leaf_rank[label];
                min_rank[v] = max_rank[v] = r;
                continue;
            }

            int l = t0.nodes[v].left;
            int r = t0.nodes[v].right;
            min_rank[v] = min(min_rank[l], min_rank[r]);
            max_rank[v] = max(max_rank[l], max_rank[r]);

            int size = t0.leaf_count[v];
            if (v == t0.root || size < min_block || size > max_block || size >= n) continue;
            if (max_rank[v] - min_rank[v] + 1 != size) continue;
            if (!t1_intervals.count(interval_key(min_rank[v], max_rank[v]))) continue;

            Candidate cand;
            cand.node = v;
            cand.size = size;
            cand.score = abs(size - int(lround(target_block)));
            candidates.push_back(cand);
        }

        sort(candidates.begin(), candidates.end(), [](const Candidate& a, const Candidate& b) {
            if (a.score != b.score) return a.score < b.score;
            if (a.size != b.size) return a.size > b.size;
            return a.node < b.node;
        });

        int covered = 0;
        for (const Candidate& cand : candidates) {
            if (int(split.nodes.size()) >= max_cuts) break;
            bool overlaps = false;
            for (int chosen : split.nodes) {
                if (t0.ancestor(chosen, cand.node) || t0.ancestor(cand.node, chosen)) {
                    overlaps = true;
                    break;
                }
            }
            if (overlaps) continue;
            if (n - (covered + cand.size) < min_block) continue;
            split.nodes.push_back(cand.node);
            covered += cand.size;
        }

        if (split.nodes.empty()) return split;

        sort(split.nodes.begin(), split.nodes.end(), [&](int a, int b) {
            return t0.leaf_l[a] < t0.leaf_l[b];
        });

        vector<char> used(n + 1, 0);
        split.sides.reserve(split.nodes.size() + 1);
        for (int node : split.nodes) {
            vector<int> labels = t0.collect_leaves(node);
            for (int label : labels) used[label] = 1;
            split.sides.push_back(move(labels));
        }

        vector<int> outside;
        outside.reserve(n - covered);
        for (int label = 1; label <= n; ++label) {
            if (!used[label]) outside.push_back(label);
        }
        if (outside.size() < size_t(min_block)) {
            split.nodes.clear();
            split.sides.clear();
            return split;
        }

        split.sides.push_back(move(outside));
        split.found = (split.sides.size() >= 3);
        if (!split.found) {
            split.nodes.clear();
            split.sides.clear();
        }
        return split;
    }

    vector<unsigned char> initial_cuts() {
        vector<unsigned char> cut = singleton_cuts();
        vector<unsigned char> merge_seed = seed_from_merge_solver();
        AnnealEval merge_eval = evaluate(merge_seed, false);
        if (merge_eval.feasible && merge_eval.components < n) cut = merge_seed;

        vector<unsigned char> common_cut = singleton_cuts();
        vector<Candidate> candidates = build_common_clade_candidates();
        vector<int> edge_used_t2(trees[1].nodes.size(), 0);
        Fenwick assigned(n);

        for (const Candidate& cand : candidates) {
            if (timer.expired()) break;
            const Tree& t0 = trees[0];
            if (assigned.sum_range(t0.leaf_l[cand.node], t0.leaf_r[cand.node]) != 0) continue;

            vector<int> labels = t0.collect_leaves(cand.node);
            vector<int> tin1 = trees[1].labels_by_tin(labels);
            Tree::Analysis a1 = trees[1].analyze_sorted_labels(tin1, interner, true);
            bool ok = true;
            for (int e : a1.edges) {
                if (edge_used_t2[e]) {
                    ok = false;
                    break;
                }
            }
            if (!ok) continue;

            if (cand.node != trees[0].root) common_cut[cand.node] = 1;
            vector<int> desc;
            collect_descendants(cand.node, desc);
            for (int v : desc) {
                if (v != cand.node) common_cut[v] = 0;
            }
            for (int label : labels) assigned.add(trees[0].leaf_rank[label], 1);
            for (int e : a1.edges) edge_used_t2[e] = 1;
        }

        AnnealEval common_eval = evaluate(common_cut, false);
        AnnealEval cur_eval = evaluate(cut, false);
        if (common_eval.feasible && common_eval.components < cur_eval.components) cut = common_cut;

        AnnealEval ev = evaluate(cut, false);
        if (!ev.feasible) {
            return singleton_cuts();
        }
        return cut;
    }

    void perturb_cut(vector<unsigned char>& cut, int flip_count) {
        if (nonroot_edges.empty()) return;
        for (int i = 0; i < flip_count; ++i) {
            int e = nonroot_edges[rnd_int(nonroot_edges.size())];
            cut[e] ^= 1;
        }
    }

    vector<unsigned char> cuts_from_components(const vector<Component>& comps) {
        vector<unsigned char> used(trees[0].nodes.size(), 0);
        for (const Component& c : comps) {
            vector<int> tin0 = trees[0].labels_by_tin(c.labels);
            Tree::Analysis a0 = trees[0].analyze_sorted_labels(tin0, interner, true);
            for (int e : a0.edges) used[e] = 1;
        }

        vector<unsigned char> cut(trees[0].nodes.size(), 0);
        for (int v : nonroot_edges) {
            if (!used[v]) cut[v] = 1;
        }
        return cut;
    }

    vector<unsigned char> seed_from_merge_solver() {
        if (timer.expired()) return singleton_cuts();
        double seed_limit = min(SEED_TIME_CAP, max(0.05, timer.limit_seconds * SEED_TIME_FRAC));
        Timer seed_timer(seed_limit);
        GreedyMergeSolver helper(seed_timer);
        helper.n = n;
        helper.trees[0] = trees[0];
        helper.trees[1] = trees[1];
        helper.interner = interner;
        vector<Component> comps = helper.solve();
        vector<unsigned char> cut = cuts_from_components(comps);
        AnnealEval ev = evaluate(cut, false);
        if (!ev.feasible) {
            VERBOSE_CERR << "# merge seed was not feasible after cut encoding; using singleton seed\n";
            return singleton_cuts();
        }
        VERBOSE_CERR << "# merge seed components " << ev.components << " seed_time_limit " << seed_limit << "\n";
        return cut;
    }

    AnnealEval evaluate(const vector<unsigned char>& cut, bool keep_components) {
        // Linear global evaluator: T1 assigns each leaf to a cut-induced component
        // and computes that component's cleaned shape. T2 then carries at most one
        // "open" component over every edge; two different open components at a node
        // certify an edge-overlap conflict.
        AnnealEval ev;
        const Tree& t0 = trees[0];
        const Tree& t1 = trees[1];
        int m0 = int(t0.nodes.size());
        int m1 = int(t1.nodes.size());

        // See evaluate_fast(): post-order node numbering means every non-root node's
        // parent index exceeds its own, so a single descending scan (parents before
        // children) replaces the top-down DFS without stack push/pop overhead.
        eval_comp_root.resize(m0);
        eval_active_roots.clear();
        eval_active_roots.push_back(t0.root);
        eval_comp_root[t0.root] = t0.root;
        eval_comp_total.resize(m0);
        eval_comp_total[t0.root] = 0;
        for (int v = m0 - 2; v >= 0; --v) {
            if (cut[v]) {
                eval_comp_root[v] = v;
                eval_comp_total[v] = 0;
                eval_active_roots.push_back(v);
            } else {
                eval_comp_root[v] = eval_comp_root[t0.nodes[v].parent];
            }
        }

        eval_sub_shape.resize(m0);
        eval_sub_count.resize(m0);
        eval_comp_shape.resize(m0);
        eval_leaf_comp.resize(n + 1);
        vector<int>& comp_root = eval_comp_root;
        vector<int>& sub_shape = eval_sub_shape;
        vector<int>& sub_count = eval_sub_count;
        vector<int>& comp_shape = eval_comp_shape;
        vector<int>& comp_total = eval_comp_total;
        vector<int>& leaf_comp = eval_leaf_comp;
        vector<int>& active_roots = eval_active_roots;
        vector<vector<int>> comp_labels;
        if (keep_components) comp_labels.assign(m0, {});

        for (int v = 0; v < m0; ++v) {
            if (t0.is_leaf(v)) {
                int label = t0.nodes[v].label;
                int c = comp_root[v];
                sub_shape[v] = label;
                sub_count[v] = 1;
                leaf_comp[label] = c;
                ++comp_total[c];
                if (keep_components) comp_labels[c].push_back(label);
            } else {
                int l = t0.nodes[v].left;
                int r = t0.nodes[v].right;
                int a = cut[l] ? 0 : sub_shape[l];
                int b = cut[r] ? 0 : sub_shape[r];
                sub_count[v] = (cut[l] ? 0 : sub_count[l]) + (cut[r] ? 0 : sub_count[r]);
                if (a == 0) sub_shape[v] = b;
                else if (b == 0) sub_shape[v] = a;
                else sub_shape[v] = interner.intern(a, b);
            }
            if ((v == t0.root || cut[v]) && sub_count[v] > 0) {
                comp_shape[v] = sub_shape[v];
            }
        }
        int active_count = 0;
        for (int c : active_roots) {
            if (sub_count[c] > 0) active_roots[active_count++] = c;
        }
        active_roots.resize(active_count);
        ev.components = int(active_roots.size());

        eval_open_comp.resize(m1);
        eval_open_count.resize(m1);
        eval_open_shape.resize(m1);
        eval_t2_shape.resize(m0);
        vector<int>& open_comp = eval_open_comp;
        vector<int>& open_count = eval_open_count;
        vector<int>& open_shape = eval_open_shape;
        vector<int>& t2_shape = eval_t2_shape;
        for (int c : active_roots) t2_shape[c] = 0;
        auto finish_component = [&](int c, int shape) {
            if (t2_shape[c] != 0 && t2_shape[c] != shape) ++ev.penalty;
            t2_shape[c] = shape;
        };

        for (int v = 0; v < m1; ++v) {
            open_comp[v] = -1;
            if (t1.is_leaf(v)) {
                int label = t1.nodes[v].label;
                int c = leaf_comp[label];
                if (c < 0) {
                    ++ev.penalty;
                    continue;
                }
                if (comp_total[c] == 1) {
                    finish_component(c, label);
                } else {
                    open_comp[v] = c;
                    open_count[v] = 1;
                    open_shape[v] = label;
                }
                continue;
            }

            int l = t1.nodes[v].left;
            int r = t1.nodes[v].right;
            int cl = open_comp[l];
            int cr = open_comp[r];
            if (cl < 0 && cr < 0) continue;
            if (cl >= 0 && cr < 0) {
                open_comp[v] = cl;
                open_count[v] = open_count[l];
                open_shape[v] = open_shape[l];
            } else if (cl < 0 && cr >= 0) {
                open_comp[v] = cr;
                open_count[v] = open_count[r];
                open_shape[v] = open_shape[r];
            } else if (cl == cr) {
                int c = cl;
                int cnt = open_count[l] + open_count[r];
                int shape = interner.intern(open_shape[l], open_shape[r]);
                if (cnt == comp_total[c]) {
                    finish_component(c, shape);
                } else {
                    open_comp[v] = c;
                    open_count[v] = cnt;
                    open_shape[v] = shape;
                }
            } else {
                ev.penalty += 2;
                if (open_count[l] >= open_count[r]) {
                    open_comp[v] = cl;
                    open_count[v] = open_count[l];
                    open_shape[v] = open_shape[l];
                } else {
                    open_comp[v] = cr;
                    open_count[v] = open_count[r];
                    open_shape[v] = open_shape[r];
                }
            }
        }

        if (open_comp[t1.root] >= 0) ev.penalty += 2;
        for (int c : active_roots) {
            if (t2_shape[c] == 0) ev.penalty += 2;
            else if (t2_shape[c] != comp_shape[c]) ev.penalty += 2 + int(comp_total[c] >= 64);

            if (keep_components) {
                Component comp;
                comp.labels = move(comp_labels[c]);
                sort(comp.labels.begin(), comp.labels.end());
                comp.id = comp_shape[c];
                ev.comps.push_back(move(comp));
            }
        }

        ev.feasible = (ev.penalty == 0);
        ev.energy = double(ev.components) + PENALTY_WEIGHT * double(ev.penalty);
        return ev;
    }

    static uint64_t poly_hash(uint64_t a, uint64_t b) {
        if (a > b) swap(a, b);
        return (a + 1) * 0x517cc1b727220a95ULL ^ (b + 1) * 0x9e3779b97f4a7c15ULL;
    }

    AnnealEval evaluate_fast(const vector<unsigned char>& cut) {
        AnnealEval ev;
        const Tree& t0 = trees[0];
        const Tree& t1 = trees[1];
        int m0 = int(t0.nodes.size());
        int m1 = int(t1.nodes.size());

        // Nodes are numbered in post-order by parse_newick (every non-root node's
        // parent index is strictly greater than its own), so a single descending
        // scan visits parents before children -- equivalent to the top-down DFS
        // this replaced, without stack push/pop overhead.
        eval_comp_root.resize(m0);
        eval_active_roots.clear();
        eval_active_roots.push_back(t0.root);
        eval_comp_root[t0.root] = t0.root;
        eval_comp_total.resize(m0);
        eval_comp_total[t0.root] = 0;
        for (int v = m0 - 2; v >= 0; --v) {
            if (cut[v]) {
                eval_comp_root[v] = v;
                eval_comp_total[v] = 0;
                eval_active_roots.push_back(v);
            } else {
                eval_comp_root[v] = eval_comp_root[t0.nodes[v].parent];
            }
        }

        fast_sub.resize(m0);
        fast_sub_count.resize(m0);
        fast_comp.resize(m0);
        eval_leaf_comp.resize(n + 1);
        for (int v = 0; v < m0; ++v) {
            if (t0.is_leaf(v)) {
                int label = t0.nodes[v].label;
                int c = eval_comp_root[v];
                fast_sub[v] = uint64_t(label);
                fast_sub_count[v] = 1;
                eval_leaf_comp[label] = c;
                ++eval_comp_total[c];
            } else {
                int l = t0.nodes[v].left, r = t0.nodes[v].right;
                uint64_t a = cut[l] ? 0 : fast_sub[l];
                uint64_t b = cut[r] ? 0 : fast_sub[r];
                fast_sub_count[v] = (cut[l] ? 0 : fast_sub_count[l]) +
                                    (cut[r] ? 0 : fast_sub_count[r]);
                if      (a == 0) fast_sub[v] = b;
                else if (b == 0) fast_sub[v] = a;
                else             fast_sub[v] = poly_hash(a, b);
            }
            if ((v == t0.root || cut[v]) && fast_sub_count[v] > 0)
                fast_comp[v] = fast_sub[v];
        }
        int active_count = 0;
        for (int c : eval_active_roots) {
            if (fast_sub_count[c] > 0) eval_active_roots[active_count++] = c;
        }
        eval_active_roots.resize(active_count);
        ev.components = active_count;

        eval_open_comp.resize(m1);
        fast_open_count.resize(m1);
        fast_open.resize(m1);
        fast_t2.resize(m0);
        for (int c : eval_active_roots) fast_t2[c] = 0;
        auto finish_comp = [&](int c, uint64_t shape) {
            if (fast_t2[c] != 0 && fast_t2[c] != shape) ++ev.penalty;
            fast_t2[c] = shape;
        };

        for (int v = 0; v < m1; ++v) {
            eval_open_comp[v] = -1;
            if (t1.is_leaf(v)) {
                int label = t1.nodes[v].label;
                int c = eval_leaf_comp[label];
                if (c < 0) { ++ev.penalty; continue; }
                if (eval_comp_total[c] == 1) finish_comp(c, uint64_t(label));
                else {
                    eval_open_comp[v] = c;
                    fast_open_count[v] = 1;
                    fast_open[v] = uint64_t(label);
                }
                continue;
            }
            int l = t1.nodes[v].left, r = t1.nodes[v].right;
            int cl = eval_open_comp[l], cr = eval_open_comp[r];
            if (cl < 0 && cr < 0) continue;
            if (cl >= 0 && cr < 0) {
                eval_open_comp[v] = cl;
                fast_open_count[v] = fast_open_count[l];
                fast_open[v] = fast_open[l];
            } else if (cl < 0 && cr >= 0) {
                eval_open_comp[v] = cr;
                fast_open_count[v] = fast_open_count[r];
                fast_open[v] = fast_open[r];
            } else if (cl == cr) {
                int cnt = fast_open_count[l] + fast_open_count[r];
                uint64_t shape = poly_hash(fast_open[l], fast_open[r]);
                if (cnt == eval_comp_total[cl]) finish_comp(cl, shape);
                else {
                    eval_open_comp[v] = cl;
                    fast_open_count[v] = cnt;
                    fast_open[v] = shape;
                }
            } else {
                ev.penalty += 2;
                if (fast_open_count[l] >= fast_open_count[r]) {
                    eval_open_comp[v] = cl;
                    fast_open_count[v] = fast_open_count[l];
                    fast_open[v] = fast_open[l];
                } else {
                    eval_open_comp[v] = cr;
                    fast_open_count[v] = fast_open_count[r];
                    fast_open[v] = fast_open[r];
                }
            }
        }

        if (eval_open_comp[t1.root] >= 0) ev.penalty += 2;
        for (int c : eval_active_roots) {
            if (fast_t2[c] == 0) ev.penalty += 2;
            else if (fast_t2[c] != fast_comp[c]) ev.penalty += 2 + int(eval_comp_total[c] >= 64);
        }

        ev.feasible = (ev.penalty == 0);
        ev.energy = ev.feasible
            ? double(ev.components)
            : double(ev.components) + PENALTY_WEIGHT * double(ev.penalty);
        return ev;
    }

    void set_cut(vector<unsigned char>& cut, int edge, unsigned char value, AnnealMove& move) {
        if (edge == trees[0].root || cut[edge] == value) return;
        move.changes.push_back({edge, cut[edge]});
        cut[edge] = value;
    }

    void rollback(vector<unsigned char>& cut, const AnnealMove& move) {
        for (int i = int(move.changes.size()) - 1; i >= 0; --i) {
            cut[move.changes[i].first] = move.changes[i].second;
        }
    }

    AnnealMove propose(vector<unsigned char>& cut, double temp = 0.0) {
        AnnealMove move;
        if (nonroot_edges.empty()) return move;
        // Temperature-adaptive swap weight: at cold T, swap moves are the only useful ones
        // (directed moves that increase energy are rejected), so boost swap proportion.
        int eff_swap = MOVE_SWAP;
        if (MOVE_SWAP_COLD_FACTOR > 1.001 && temp < TEMP_END * 4.0) {
            double cold_frac = max(0.0, min(1.0, 1.0 - temp / max(1e-9, TEMP_END * 4.0)));
            eff_swap = (int)(MOVE_SWAP * (1.0 + (MOVE_SWAP_COLD_FACTOR - 1.0) * cold_frac) + 0.5);
        }
        int total_weight = MOVE_TOGGLE + MOVE_REMOVE + MOVE_ADD +
                           MOVE_PAIR_REMOVE + eff_swap + MOVE_SIBLING_SWAP +
                           MOVE_LEVEL_SWAP;
        int kind = rnd_int(total_weight);
        int remove_end = MOVE_TOGGLE + MOVE_REMOVE;
        int add_end = remove_end + MOVE_ADD;
        int pair_remove_end = add_end + MOVE_PAIR_REMOVE;
        int swap_end = pair_remove_end + eff_swap;
        int sibling_end = swap_end + MOVE_SIBLING_SWAP;
        int level_end = sibling_end + MOVE_LEVEL_SWAP;

        if (kind < MOVE_TOGGLE) {
            int e = nonroot_edges[rnd_int(nonroot_edges.size())];
            set_cut(cut, e, cut[e] ? 0 : 1, move);
        } else if (kind < remove_end) {
            for (int tries = 0; tries < 30 && move.changes.empty(); ++tries) {
                int e = nonroot_edges[rnd_int(nonroot_edges.size())];
                if (cut[e]) set_cut(cut, e, 0, move);
            }
        } else if (kind < add_end) {
            for (int tries = 0; tries < 30 && move.changes.empty(); ++tries) {
                int e = nonroot_edges[rnd_int(nonroot_edges.size())];
                if (!cut[e]) set_cut(cut, e, 1, move);
            }
        } else if (kind < pair_remove_end) {
            int e1 = -1;
            for (int tries = 0; tries < 30; ++tries) {
                int e = nonroot_edges[rnd_int(nonroot_edges.size())];
                if (cut[e]) {
                    e1 = e;
                    set_cut(cut, e, 0, move);
                    break;
                }
            }
            if (e1 >= 0) {
                bool found = false;
                int guide = rnd_int(12);
                if (guide <= 3 && !t1_sorted_edges.empty()) {
                    int rank1 = t1_min_rank_vec[e1];
                    int rlo = max(0, rank1 - pair_window);
                    int rhi = min(n, rank1 + pair_window);
                    int lo_idx = int(lower_bound(t1_sorted_edges.begin(), t1_sorted_edges.end(), rlo,
                        [&](int e, int val) { return t1_min_rank_vec[e] < val; }) - t1_sorted_edges.begin());
                    int hi_idx = int(upper_bound(t1_sorted_edges.begin(), t1_sorted_edges.end(), rhi,
                        [&](int val, int e) { return val < t1_min_rank_vec[e]; }) - t1_sorted_edges.begin());
                    if (hi_idx > lo_idx) {
                        for (int tries = 0; tries < 20; ++tries) {
                            int e2 = t1_sorted_edges[lo_idx + rnd_int(hi_idx - lo_idx)];
                            if (cut[e2]) {
                                set_cut(cut, e2, 0, move);
                                found = true;
                                break;
                            }
                        }
                    }
                } else if (guide <= 5 && !t1_sorted_edges.empty()) {
                    int hi_rank = t1_max_rank_vec[e1];
                    int pos1 = t1_edge_pos[e1];
                    int msz = int(t1_sorted_edges.size());
                    for (int tries = 0; tries < 20; ++tries) {
                        int pos2 = min(msz - 1, pos1 + rnd_int(pair_window) + 1);
                        int e2 = t1_sorted_edges[pos2];
                        if (cut[e2] && t1_max_rank_vec[e2] <= hi_rank) {
                            set_cut(cut, e2, 0, move);
                            found = true;
                            break;
                        }
                    }
                } else if (guide <= 7 && !t1_sorted_edges.empty()) {
                    int hi_rank = t1_max_rank_vec[e1];
                    int pos1 = t1_edge_pos[e1];
                    for (int tries = 0; tries < 20; ++tries) {
                        int pos2 = max(0, pos1 - (rnd_int(pair_window) + 1));
                        int e2 = t1_sorted_edges[pos2];
                        if (cut[e2] && t1_max_rank_vec[e2] >= hi_rank) {
                            set_cut(cut, e2, 0, move);
                            found = true;
                            break;
                        }
                    }
                } else if (guide == 8 && !t1_sorted_edges.empty()) {
                    int succ = t1_max_rank_vec[e1] + 1;
                    int rlo = succ;
                    int rhi = min(n, succ + pair_window);
                    int lo_idx = int(lower_bound(t1_sorted_edges.begin(), t1_sorted_edges.end(), rlo,
                        [&](int e, int val) { return t1_min_rank_vec[e] < val; }) - t1_sorted_edges.begin());
                    int hi_idx = int(upper_bound(t1_sorted_edges.begin(), t1_sorted_edges.end(), rhi,
                        [&](int val, int e) { return val < t1_min_rank_vec[e]; }) - t1_sorted_edges.begin());
                    if (hi_idx > lo_idx) {
                        for (int tries = 0; tries < 20; ++tries) {
                            int e2 = t1_sorted_edges[lo_idx + rnd_int(hi_idx - lo_idx)];
                            if (cut[e2]) {
                                set_cut(cut, e2, 0, move);
                                found = true;
                                break;
                            }
                        }
                    }
                } else if (guide == 9 && !t0_sorted_edges.empty()) {
                    int succ0 = t0_max_rank_vec[e1] + 1;
                    int rlo = succ0;
                    int rhi = min(n, succ0 + pair_window);
                    int lo_idx = int(lower_bound(t0_sorted_edges.begin(), t0_sorted_edges.end(), rlo,
                        [&](int e, int val) { return t0_min_rank_vec[e] < val; }) - t0_sorted_edges.begin());
                    int hi_idx = int(upper_bound(t0_sorted_edges.begin(), t0_sorted_edges.end(), rhi,
                        [&](int val, int e) { return val < t0_min_rank_vec[e]; }) - t0_sorted_edges.begin());
                    if (hi_idx > lo_idx) {
                        for (int tries = 0; tries < 20; ++tries) {
                            int e2 = t0_sorted_edges[lo_idx + rnd_int(hi_idx - lo_idx)];
                            if (cut[e2]) {
                                set_cut(cut, e2, 0, move);
                                found = true;
                                break;
                            }
                        }
                    }
                } else if (guide == 10 && !t0_sorted_edges.empty()) {
                    int hi0 = t0_max_rank_vec[e1];
                    int pos1 = t0_edge_pos[e1];
                    int msz = int(t0_sorted_edges.size());
                    for (int tries = 0; tries < 20; ++tries) {
                        int pos2 = min(msz - 1, pos1 + rnd_int(pair_window) + 1);
                        int e2 = t0_sorted_edges[pos2];
                        if (cut[e2] && t0_max_rank_vec[e2] <= hi0) {
                            set_cut(cut, e2, 0, move);
                            found = true;
                            break;
                        }
                    }
                } else if (guide == 11 && !t0_sorted_edges.empty()) {
                    int hi0 = t0_max_rank_vec[e1];
                    int pos1 = t0_edge_pos[e1];
                    for (int tries = 0; tries < 20; ++tries) {
                        int pos2 = max(0, pos1 - (rnd_int(pair_window) + 1));
                        int e2 = t0_sorted_edges[pos2];
                        if (cut[e2] && t0_max_rank_vec[e2] >= hi0) {
                            set_cut(cut, e2, 0, move);
                            found = true;
                            break;
                        }
                    }
                }
                if (!found) {
                    for (int tries = 0; tries < 30; ++tries) {
                        int e = nonroot_edges[rnd_int(nonroot_edges.size())];
                        if (!cut[e]) continue;
                        bool seen = false;
                        for (const auto& ch : move.changes) {
                            if (ch.first == e) {
                                seen = true;
                                break;
                            }
                        }
                        if (!seen) {
                            set_cut(cut, e, 0, move);
                            break;
                        }
                    }
                }
            }
        } else if (kind < swap_end) {
            int e1 = -1;
            for (int tries = 0; tries < 30; ++tries) {
                int e = nonroot_edges[rnd_int(nonroot_edges.size())];
                if (cut[e]) {
                    e1 = e;
                    break;
                }
            }
            if (e1 >= 0) {
                bool found_e2 = false;
                if (!t1_sorted_edges.empty()) {
                    int rank1 = t1_min_rank_vec[e1];
                    int rlo = max(0, rank1 - pair_window);
                    int rhi = min(n, rank1 + pair_window);
                    int lo_idx = int(lower_bound(t1_sorted_edges.begin(), t1_sorted_edges.end(), rlo,
                        [&](int e, int val) { return t1_min_rank_vec[e] < val; }) - t1_sorted_edges.begin());
                    int hi_idx = int(upper_bound(t1_sorted_edges.begin(), t1_sorted_edges.end(), rhi,
                        [&](int val, int e) { return val < t1_min_rank_vec[e]; }) - t1_sorted_edges.begin());
                    if (hi_idx > lo_idx) {
                        for (int tries = 0; tries < 20; ++tries) {
                            int e2 = t1_sorted_edges[lo_idx + rnd_int(hi_idx - lo_idx)];
                            if (!cut[e2]) {
                                set_cut(cut, e1, 0, move);
                                set_cut(cut, e2, 1, move);
                                found_e2 = true;
                                break;
                            }
                        }
                    }
                }
                if (!found_e2) {
                    set_cut(cut, e1, 0, move);
                }
            }
        } else if (kind < sibling_end) {
            // Sibling swap: exchange a cut edge with its sibling in T1 (very local rearrangement).
            // Moving a cut between siblings changes which branch of a fork is separated,
            // allowing fine-grained alignment with T2 topology.
            for (int tries = 0; tries < 30; ++tries) {
                int e = nonroot_edges[rnd_int(nonroot_edges.size())];
                if (!cut[e]) continue;
                int p = trees[0].nodes[e].parent;
                if (p < 0 || p == trees[0].root) continue;
                int sib = (trees[0].nodes[p].left == e) ? trees[0].nodes[p].right : trees[0].nodes[p].left;
                if (sib >= 0 && sib != e && !cut[sib]) {
                    set_cut(cut, e, 0, move);
                    set_cut(cut, sib, 1, move);
                    break;
                }
            }
        } else if (kind < level_end) {
            // Level swap: move a cut one level up (to parent) or down (to a child) in T1.
            // Explores vertical neighborhood: complements sibling_swap's horizontal moves.
            for (int tries = 0; tries < 30; ++tries) {
                int e = nonroot_edges[rnd_int(nonroot_edges.size())];
                if (!cut[e]) continue;
                if (tries % 2 == 0) {
                    // Ancestor swap: uncut e, cut its parent edge
                    int p = trees[0].nodes[e].parent;
                    if (p < 0 || p == trees[0].root || cut[p]) continue;
                    set_cut(cut, e, 0, move);
                    set_cut(cut, p, 1, move);
                    break;
                } else {
                    // Descendant swap: uncut e, cut one of its child edges
                    int left = trees[0].nodes[e].left;
                    int right = trees[0].nodes[e].right;
                    bool lo = (left >= 0 && !cut[left]);
                    bool ro = (right >= 0 && !cut[right]);
                    int target = -1;
                    if (lo && ro) target = rnd01() < 0.5 ? left : right;
                    else if (lo) target = left;
                    else if (ro) target = right;
                    if (target < 0) continue;
                    set_cut(cut, e, 0, move);
                    set_cut(cut, target, 1, move);
                    break;
                }
            }
        } else {
            // (unused — weight 0)
        }

        return move;
    }

    void greedy_finish(vector<unsigned char>& cut, AnnealEval& cur, vector<unsigned char>& best_cut,
                       AnnealEval& best, double stop_time = -1.0) {
        vector<int> order = nonroot_edges;
        bool changed = true;
        auto stopped = [&]() {
            return timer.expired() || (stop_time >= 0.0 && timer.elapsed() >= stop_time);
        };
        while (changed && !stopped()) {
            changed = false;
            for (int i = int(order.size()) - 1; i > 0; --i) swap(order[i], order[rnd_int(i + 1)]);
            for (int e : order) {
                if (!cut[e] || stopped()) continue;
                cut[e] = 0;
                AnnealEval next = evaluate_fast(cut);
                if (next.feasible && next.components < cur.components) {
                    cur = next;
                    changed = true;
                    if (cur.components < best.components) {
                        best = cur;
                        best_cut = cut;
                    }
                } else {
                    cut[e] = 1;
                }
            }
        }
    }

    // Exact greedy using full evaluate() — safe for tie-acceptance (no hash false-positives).
    // Accepts equal-cost merges so it can rearrange cuts to unlock new merges on the next pass.
    // Slower than greedy_finish (O(n) per step vs O(hash)), use for post-SA polish only.
    void greedy_finish_exact(vector<unsigned char>& cut, AnnealEval& cur, vector<unsigned char>& best_cut,
                             AnnealEval& best, double stop_time = -1.0) {
        vector<int> order = nonroot_edges;
        bool changed = true;
        int tie_only_rounds = 0;
        auto stopped = [&]() {
            return timer.expired() || (stop_time >= 0.0 && timer.elapsed() >= stop_time);
        };
        while (changed && !stopped()) {
            changed = false;
            bool any_strict = false;
            for (int i = int(order.size()) - 1; i > 0; --i) swap(order[i], order[rnd_int(i + 1)]);
            for (int e : order) {
                if (!cut[e] || stopped()) continue;
                cut[e] = 0;
                AnnealEval next = evaluate(cut, false);
                // exact evaluate() — safe to accept ties (no hash collisions)
                if (next.feasible && next.components <= cur.components) {
                    if (next.components < cur.components) any_strict = true;
                    cur = next;
                    changed = true;
                    if (cur.components < best.components) {
                        best = cur;
                        best_cut = cut;
                    }
                } else {
                    cut[e] = 1;
                }
            }
            if (!any_strict) {
                if (++tie_only_rounds >= 3) changed = false;
            } else {
                tie_only_rounds = 0;
            }
        }
    }

    // Post-greedy swap refinement: try sibling/ancestor/descendant swaps, accept strict
    // improvements only. Followed by another removal-greedy pass to exploit new state.
    // Only runs if time remains after greedy convergence (harmless for large n).
    void swap_greedy_finish(vector<unsigned char>& cut, AnnealEval& cur,
                            vector<unsigned char>& best_cut, AnnealEval& best,
                            double stop_time) {
        auto stopped = [&]() {
            return timer.expired() || (stop_time >= 0.0 && timer.elapsed() >= stop_time);
        };
        auto try_swap = [&](int remove_e, int add_e) -> bool {
            cut[remove_e] = 0; cut[add_e] = 1;
            AnnealEval nx = evaluate(cut, false);
            if (nx.feasible && nx.components < cur.components) {
                cur = nx;
                if (cur.components < best.components) { best = cur; best_cut = cut; }
                return true;
            }
            cut[remove_e] = 1; cut[add_e] = 0;
            return false;
        };
        bool outer_changed = true;
        while (outer_changed && !stopped()) {
            outer_changed = false;
            vector<int> order = nonroot_edges;
            for (int i = int(order.size()) - 1; i > 0; --i) swap(order[i], order[rnd_int(i + 1)]);
            for (int e : order) {
                if (!cut[e] || stopped()) continue;
                bool found = false;
                int p  = trees[0].nodes[e].parent;
                // Sibling swap (1 hop horizontal)
                if (!found && p >= 0 && p != trees[0].root) {
                    int sib = (trees[0].nodes[p].left == e) ? trees[0].nodes[p].right : trees[0].nodes[p].left;
                    if (sib >= 0 && sib != e && !cut[sib])
                        found = try_swap(e, sib);
                }
                // Ancestor swap (1 level up)
                if (!found && p >= 0 && p != trees[0].root && !cut[p])
                    found = try_swap(e, p);
                // Grandparent swap (2 levels up)
                if (!found && p >= 0 && p != trees[0].root) {
                    int gp = trees[0].nodes[p].parent;
                    if (gp >= 0 && gp != trees[0].root && !cut[gp])
                        found = try_swap(e, gp);
                }
                // Descendant swaps (1 level down)
                for (int child : {trees[0].nodes[e].left, trees[0].nodes[e].right}) {
                    if (found || child < 0 || cut[child] || stopped()) continue;
                    found = try_swap(e, child);
                }
                // Grandchild swaps (2 levels down)
                for (int child : {trees[0].nodes[e].left, trees[0].nodes[e].right}) {
                    if (found || child < 0 || cut[child] || stopped()) continue;
                    for (int gc : {trees[0].nodes[child].left, trees[0].nodes[child].right}) {
                        if (found || gc < 0 || cut[gc]) continue;
                        found = try_swap(e, gc);
                    }
                }
                if (found) outer_changed = true;
            }
            // If any swap improved, re-run removal greedy to exploit new state
            if (outer_changed && !stopped()) {
                greedy_finish_exact(cut, cur, best_cut, best, stop_time);
            }
        }
    }

    struct SearchState {
        vector<unsigned char> cut;
        vector<unsigned char> best_cut;
        AnnealEval cur;
        AnnealEval best;
        long long iterations = 0;
        long long accepted = 0;
        long long accepted_worse = 0;
        long long valid_improvements = 0;
        double temp = 0.0;
        double anneal_start = 0.0;
        double anneal_budget = 0.001;
        double anneal_stop_time = 0.0;
        double last_diag_time = 0.0;
        double last_improvement_time = 0.0;
        long long last_diag_iterations = 0;
        bool initialized = false;
    };

    SearchState restart_search_from_cut(
        const vector<unsigned char>& initial_cut,
        const AnnealEval& global_best_eval,
        const vector<unsigned char>& global_best_cut,
        double stop_time)
    {
        SearchState st;
        if (newicks.size() != 2) return st;

        st.cut = initial_cut;
        st.cur = evaluate(st.cut, false);
        if (!st.cur.feasible) {
            st.cut = global_best_cut;
            st.cur = global_best_eval;
        }

        st.best = global_best_eval;
        st.best_cut = global_best_cut;
        if (st.cur.feasible && (!st.best.feasible || st.cur.components < st.best.components)) {
            st.best = st.cur;
            st.best_cut = st.cut;
        }

        st.temp = TEMP_START;
        st.anneal_start = timer.elapsed();
        st.anneal_stop_time = stop_time;
        st.anneal_budget = max(0.001, stop_time - st.anneal_start);
        st.last_diag_time = st.anneal_start;
        st.last_improvement_time = st.anneal_start;
        st.last_diag_iterations = 0;
        st.initialized = true;

        VERBOSE_CERR << "# sa restart components " << st.cur.components
             << " best " << st.best.components
             << " leaves " << n << "\n";
        return st;
    }

    void emit_progress_diagnostic(SearchState& st, bool force = false) {
        if (!st.initialized) return;
        double now = timer.elapsed();
        if (!force) {
            if (DIAG_INTERVAL <= 0.0) return;
            if (now - st.last_diag_time < DIAG_INTERVAL) return;
        }
        double anneal_elapsed = max(0.0, now - st.anneal_start);
        double avg_iter_us = st.iterations > 0
                             ? anneal_elapsed * 1e6 / double(st.iterations)
                             : 0.0;
        double avg_iter_ns_per_leaf = (st.iterations > 0 && n > 0)
                                      ? anneal_elapsed * 1e9 / (double(st.iterations) * double(n))
                                      : 0.0;
        long long interval_iterations = max(0LL, st.iterations - st.last_diag_iterations);
        double interval_seconds = max(1e-9, now - st.last_diag_time);
        double interval_iter_us = interval_iterations > 0
                                  ? interval_seconds * 1e6 / double(interval_iterations)
                                  : 0.0;
        VERBOSE_CERR << "# sa progress solver_id " << reinterpret_cast<uintptr_t>(this)
             << " time " << now
             << " anneal_elapsed " << anneal_elapsed
             << " leaves " << n
             << " iterations " << st.iterations
             << " current_cost " << st.cur.energy
             << " current_components " << st.cur.components
             << " current_penalty " << st.cur.penalty
             << " current_feasible " << (st.cur.feasible ? 1 : 0)
             << " temperature " << st.temp
             << " avg_iter_us " << avg_iter_us
             << " avg_iter_ns_per_leaf " << avg_iter_ns_per_leaf
             << " interval_iter_us " << interval_iter_us
             << " accepted " << st.accepted
             << " accepted_worse " << st.accepted_worse << "\n";
        st.last_diag_time = now;
        st.last_diag_iterations = st.iterations;
    }

    SearchState start_search() {
        SearchState st;

        st.cut = initial_cuts();
        st.cur = evaluate(st.cut, false);
        if (!st.cur.feasible) {
            st.cut = singleton_cuts();
            st.cur = evaluate(st.cut, false);
        }

        // Pre-SA greedy: polish initial state before SA. n<=1000: exact greedy (tie-aware).
        // n<=2000: fast greedy (approximate but cheaper) for a moderate warm-start.
        if (st.cur.feasible && !timer.expired()) {
            double pre_greedy_limit = timer.elapsed() + min(0.5, timer.limit_seconds * 0.03);
            st.best_cut = st.cut;
            st.best = st.cur;
            if (n <= 1000) {
                greedy_finish_exact(st.cut, st.cur, st.best_cut, st.best, pre_greedy_limit);
            } else if (n <= 2000) {
                greedy_finish(st.cut, st.cur, st.best_cut, st.best, pre_greedy_limit);
            }
            VERBOSE_CERR << "# sa preseed_greedy components " << st.best.components << " leaves " << n << "\n";
        }

        st.best_cut = st.cut;
        st.best = st.cur;
        st.temp = TEMP_START;
        st.anneal_start = timer.elapsed();
        double time_limit = timer.limit_seconds;
        double polish_budget = min(POLISH_TIME_CAP, max(0.0, time_limit * POLISH_TIME_FRAC));
        st.anneal_stop_time = max(st.anneal_start, time_limit - polish_budget);
        st.anneal_budget = max(0.001, st.anneal_stop_time - st.anneal_start);
        st.last_diag_time = st.anneal_start;
        st.last_improvement_time = st.anneal_start;
        st.last_diag_iterations = st.iterations;
        st.initialized = true;

        VERBOSE_CERR << "# sa initial components " << st.cur.components
             << " leaves " << n
             << " temp_start " << TEMP_START
             << " temp_end " << TEMP_END
             << " penalty " << PENALTY_WEIGHT
             << " diag_interval " << DIAG_INTERVAL
             << " polish " << POLISH_TIME_FRAC << "/"
             << POLISH_TIME_CAP
             << " swap_trees " << SWAP_TREES
             << " reductions " << REDUCE_CHAIN << "/"
             << REDUCE_THREE_TWO
             << " moves " << MOVE_TOGGLE << "/"
             << MOVE_REMOVE << "/"
             << MOVE_ADD << "/"
             << MOVE_PAIR_REMOVE << "/"
             << MOVE_SWAP << "/"
             << MOVE_SIBLING_SWAP << "/"
             << MOVE_LEVEL_SWAP << "\n";

        emit_progress_diagnostic(st, true);
        return st;
    }

    bool anneal_step(SearchState& st) {
        if (!st.initialized || timer.expired() || timer.elapsed() >= st.anneal_stop_time) return false;

        if ((st.iterations & 31) == 0) {
            double elapsed = timer.elapsed();
            double frac = min(1.0, elapsed / max(0.001, timer.limit_seconds));
            st.temp = TEMP_START * pow(TEMP_END / TEMP_START, frac);
        }

        AnnealMove move = propose(st.cut, st.temp);
        if (move.changes.empty()) {
            ++st.iterations;
            emit_progress_diagnostic(st);
            return true;
        }

        // propose() already applied the move to st.cut via set_cut.
        // Fast evaluate on every step, exact-validate before committing an incumbent.
        // evaluate_fast uses hashes for shape equality; keeping exact validation on
        // best updates avoids submitting a hash false-positive solution.
        double old_energy = st.cur.energy;
        AnnealEval new_eval = evaluate_fast(st.cut);
        double delta = new_eval.energy - old_energy;
        bool take = delta <= 0.0 || rnd01() < exp(-delta / max(1e-9, st.temp));
        if (take) {
            if (delta > 0.0) ++st.accepted_worse;
            ++st.accepted;
            st.cur = new_eval;
            if (st.cur.feasible && st.cur.components < st.best.components) {
                AnnealEval exact_eval = evaluate(st.cut, false);
                st.cur = exact_eval;
                if (st.cur.feasible && st.cur.components < st.best.components) {
                    st.best = st.cur;
                    st.best_cut = st.cut;
                    ++st.valid_improvements;
                    st.last_improvement_time = timer.elapsed();
                }
            }
        } else {
            rollback(st.cut, move);
        }
        ++st.iterations;
        emit_progress_diagnostic(st);
        return true;
    }

    void finish_search(SearchState& st, double stop_time = -1.0) {
        if (!st.initialized) return;
        auto stopped = [&]() {
            return timer.expired() || (stop_time >= 0.0 && timer.elapsed() >= stop_time);
        };
        auto time_remaining = [&]() -> double {
            if (timer.expired()) return 0.0;
            if (stop_time >= 0.0) return max(0.0, stop_time - timer.elapsed());
            return max(0.0, timer.limit_seconds - timer.elapsed());
        };

        if (st.best.feasible && !stopped()) {
            st.cut = st.best_cut;
            st.cur = st.best;
            double rem = time_remaining();
            double ils_reserve;
            if (rem >= 4.0) {
                ils_reserve = min(rem - 2.0, 4.0);  // Large budget: greedy gets min 2.0s.
            } else if (rem >= 1.5) {
                ils_reserve = rem - 1.0;  // Smaller budget: greedy gets 1.0s, ILS gets rest.
            } else {
                ils_reserve = 0.0;
            }
            double greedy_stop = (stop_time < 0.0 ? timer.limit_seconds : stop_time) - ils_reserve;
            greedy_finish_exact(st.cut, st.cur, st.best_cut, st.best, greedy_stop);
            // Swap greedy: try sibling/level swaps after removal convergence.
            // Only runs for small/medium n where greedy finishes with time to spare.
            if (!stopped() && timer.elapsed() < greedy_stop) {
                swap_greedy_finish(st.cut, st.cur, st.best_cut, st.best, greedy_stop);
            }
        }

        // ILS: use remaining time for iterated local search.
        long long ils_improvements = 0;
        int ils_cycles = 0;
        // ILS baseline: best components from exact evaluate (always initialized if feasible).
        int ils_true_best_comp = st.best.feasible
            ? evaluate(st.best_cut, false).components : INT_MAX;
        vector<unsigned char> ils_true_best_cut = st.best_cut;
        while (!stopped() && st.best.feasible && time_remaining() >= 1.0 && ils_true_best_comp < INT_MAX) {
            ++ils_cycles;
            double cycle_start = timer.elapsed();
            double rem = time_remaining();
            // Each cycle uses up to 1/5 of remaining time, capped at 15s, min 0.5s.
            // Using 1/5 instead of 1/3 allows more cycles and perturbation diversity.
            double cycle_budget = min(15.0, max(0.5, rem / 5.0));

            // Alternate small and large perturbations.
            int k_small = max(1, int(sqrt(double(max(1, ils_true_best_comp)) / 10.0)));
	        int k_large = max(k_small + 1, int(sqrt(double(n))));
	        int k = (ils_cycles % 2 == 1) ? k_small : k_large;
            // Perturb from the true best (not fast-best, to avoid drifting).
            st.cut = ils_true_best_cut;
            for (int i = 0; i < k; ++i) {
		        if (nonroot_edges.empty()) break;
                int cut_e = -1, uncut_e = -1;
                for (int t = 0; t < 30 && cut_e < 0; ++t) {
                    int e = nonroot_edges[rnd_int(nonroot_edges.size())];
                    if (st.cut[e]) cut_e = e;
                }
                for (int t = 0; t < 30 && uncut_e < 0; ++t) {
                    int e = nonroot_edges[rnd_int(nonroot_edges.size())];
                    if (!st.cut[e]) uncut_e = e;
                }
                if (cut_e >= 0 && uncut_e >= 0) { st.cut[cut_e] = 0; st.cut[uncut_e] = 1; }
                else if (cut_e >= 0) st.cut[cut_e] ^= 1;
            }
            // Resync state after perturbation using exact evaluate.
            st.cur = evaluate(st.cut, false);
            // Exact greedy polish from perturbed state: safe with tie acceptance.
            greedy_finish_exact(st.cut, st.cur, ils_true_best_cut, st.best, stop_time);
            // Check if greedy found improvement (evaluate() is exact, no validation needed).
            if (st.cur.feasible && st.cur.components < ils_true_best_comp) {
                ils_true_best_comp = st.cur.components;
                ils_true_best_cut = st.cut;
                st.best_cut = st.cut;
                st.best.components = st.cur.components;
                st.best.feasible = true;
                st.best.energy = double(st.cur.components);
                ++st.valid_improvements;
                ++ils_improvements;
            }
            // Use post-greedy state as reference for the mini-SA acceptance criterion.
            AnnealEval fast_cycle_best = st.cur;
            vector<unsigned char> fast_cycle_best_cut = st.cut;

            // Mini-SA: full geometric cooling from temp_start to temp_end over cycle_budget.
            while (!stopped()) {
                double in_cycle = timer.elapsed() - cycle_start;
                if (in_cycle >= cycle_budget) break;

                if ((st.iterations & 31) == 0) {
                    double frac = min(1.0, in_cycle / cycle_budget);
                    st.temp = TEMP_START * pow(TEMP_END / TEMP_START, frac);
                }

                AnnealMove move = propose(st.cut, st.temp);
                if (move.changes.empty()) { ++st.iterations; continue; }

                double ils_old_e = st.cur.energy;
                AnnealEval ils_new_eval = evaluate(st.cut, false);
                double delta = ils_new_eval.energy - ils_old_e;
                bool take = delta <= 0.0 || rnd01() < exp(-delta / max(1e-9, st.temp));
                if (take) {
                    ++st.accepted;
                    if (delta > 0.0) ++st.accepted_worse;
                    st.cur = ils_new_eval;
                    if (st.cur.feasible && st.cur.components < fast_cycle_best.components) {
                        fast_cycle_best = st.cur;
                        fast_cycle_best_cut = st.cut;
                    }
                } else {
                    rollback(st.cut, move);
                }
                ++st.iterations;
            }

            // Mini-SA best: evaluate() is exact since SA loop now uses evaluate().
            if (fast_cycle_best.feasible && fast_cycle_best.components < ils_true_best_comp) {
                ils_true_best_comp = fast_cycle_best.components;
                ils_true_best_cut = fast_cycle_best_cut;
                st.best_cut = fast_cycle_best_cut;
                st.best.components = fast_cycle_best.components;
                st.best.feasible = true;
                st.best.energy = double(fast_cycle_best.components);
                ++st.valid_improvements;
                ++ils_improvements;
            }

            // Exact greedy polish from the cycle's best state.
            if (st.best.feasible && !stopped()) {
                st.cut = ils_true_best_cut;
                st.cur = st.best;
                greedy_finish_exact(st.cut, st.cur, ils_true_best_cut, st.best, stop_time);
                if (st.best.components < ils_true_best_comp) {
                    ils_true_best_comp = st.best.components;
                    ils_true_best_cut = st.cut;
                }
            }
        }
        // Ensure final best uses the validated true best.
        if (ils_true_best_comp < INT_MAX) {
            st.best_cut = ils_true_best_cut;
        }

        double total_elapsed = max(1e-9, timer.elapsed());
        VERBOSE_CERR << "# sa final best " << st.best.components
             << " leaves " << n
             << " iterations " << st.iterations
             << " iter_per_sec " << static_cast<long long>(double(st.iterations) / total_elapsed)
             << " accepted " << st.accepted
             << " accepted_worse " << st.accepted_worse
             << " valid_improvements " << st.valid_improvements
             << " ils_cycles " << ils_cycles
             << " ils_improvements " << ils_improvements << "\n";
    }

    vector<Component> components_from_search(const SearchState& st) {
        if (!st.initialized) return singleton_solution();
        AnnealEval out = evaluate(st.best_cut, true);
        if (!out.feasible) return singleton_solution();
        sort(out.comps.begin(), out.comps.end(), [](const Component& a, const Component& b) {
            return a.labels.front() < b.labels.front();
        });
        return out.comps;
    }

    vector<Component> solve() {
        SearchState st = start_search();
        while (anneal_step(st)) {}
        finish_search(st);
        return components_from_search(st);
    }

    vector<Component> singleton_solution() const {
        vector<Component> comps;
        comps.reserve(n);
        for (int label = 1; label <= n; ++label) {
            Component c;
            c.labels = {label};
            c.id = label;
            comps.push_back(move(c));
        }
        return comps;
    }

    vector<string> solution_lines(const vector<Component>& comps) const {
        if (reductions.active) {
            vector<string> lines = reductions.expand_to_newicks(comps);
            if (!lines.empty()) return lines;
        }
        vector<string> lines;
        lines.reserve(comps.size());
        for (const Component& c : comps) lines.push_back(interner.to_newick(c.id));
        return lines;
    }

};

struct RawInput {
    int n = 0;
    int trees = 0;
    vector<string> newicks;
};

static RawInput read_raw_input() {
    RawInput input;
    string line;
    while (getline(cin, line)) {
        if (line.empty()) continue;
        if (line[0] == '#') {
            if (line.rfind("#p ", 0) == 0) {
                size_t p = line.find(' ', 3);
                input.trees = stoi(line.substr(3, p - 3));
                input.n = stoi(line.substr(p + 1));
            }
            continue;
        }
        input.newicks.push_back(line);
        if (input.trees > 0 && int(input.newicks.size()) >= input.trees) break;
    }
    if (input.n == 0) input.n = AnnealSolver::infer_leaf_count(input.newicks);
    if (input.trees == 0) input.trees = int(input.newicks.size());
    assert(input.trees == 2);
    return input;
}

static string relabel_newick(const string& s, const vector<int>& relabel) {
    string out;
    out.reserve(s.size() + 16);
    for (size_t i = 0; i < s.size();) {
        if ('0' <= s[i] && s[i] <= '9') {
            int value = 0;
            while (i < s.size() && '0' <= s[i] && s[i] <= '9') {
                value = 10 * value + (s[i] - '0');
                ++i;
            }
            int mapped = (0 <= value && value < int(relabel.size()) && relabel[value] > 0)
                         ? relabel[value] : value;
            out += to_string(mapped);
        } else {
            out.push_back(s[i++]);
        }
    }
    return out;
}

static vector<int> labels_from_newick(const string& s) {
    vector<int> labels;
    for (size_t i = 0; i < s.size();) {
        if ('0' <= s[i] && s[i] <= '9') {
            int value = 0;
            while (i < s.size() && '0' <= s[i] && s[i] <= '9') {
                value = 10 * value + (s[i] - '0');
                ++i;
            }
            if (value > 0) labels.push_back(value);
        } else {
            ++i;
        }
    }
    sort(labels.begin(), labels.end());
    labels.erase(unique(labels.begin(), labels.end()), labels.end());
    return labels;
}

static vector<Component> components_from_newick_lines(const vector<string>& lines) {
    vector<Component> comps;
    comps.reserve(lines.size());
    for (const string& line : lines) {
        Component c;
        c.labels = labels_from_newick(line);
        if (!c.labels.empty()) {
            c.id = c.labels.front();
            comps.push_back(move(c));
        }
    }
    return comps;
}

static string induced_newick(const Tree& tree, const vector<int>& labels,
                             const vector<int>& old_to_local) {
    if (labels.empty()) return ";";
    Interner tmp;
    tmp.reset(tree.n);
    vector<int> tin_labels = tree.labels_by_tin(labels);
    Tree::Analysis a = tree.analyze_sorted_labels(tin_labels, tmp, false);
    return relabel_newick(tmp.to_newick(a.id), old_to_local) + ";";
}

struct ClusterManager {
    struct Node {
        unique_ptr<AnnealSolver> solver;
        vector<unique_ptr<Node>> children;
        vector<vector<int>> child_to_parent;
        AnnealSolver::SearchState state;
        bool state_started = false;
    };

    Timer& timer;
    uint64_t rng = RANDOM_SEED ^ 0x6a09e667f3bcc909ULL;
    vector<Node*> leaves;
    int node_count = 0;
    int split_count = 0;
    int projected_blocks = 1;

    explicit ClusterManager(Timer& t) : timer(t) {}

    uint64_t next_rand() {
        rng ^= rng << 7;
        rng ^= rng >> 9;
        return rng;
    }

    double rnd01() {
        return double(next_rand() >> 11) * (1.0 / 9007199254740992.0);
    }

    bool can_add_split(int side_count) const {
        if (side_count <= 1) return false;
        return projected_blocks + side_count - 1 <= CLUSTER_MAX_BLOCKS;
    }

    void split_node(Node* node, vector<vector<int>> sides, int depth) {
        projected_blocks += int(sides.size()) - 1;
        for (vector<int>& side : sides) {
            vector<int> old_to_local(node->solver->n + 1, 0);
            vector<int> child_to_parent(side.size() + 1, 0);
            for (int i = 0; i < int(side.size()); ++i) {
                old_to_local[side[i]] = i + 1;
                child_to_parent[i + 1] = side[i];
            }

            vector<string> child_newicks = {
                induced_newick(node->solver->trees[0], side, old_to_local),
                induced_newick(node->solver->trees[1], side, old_to_local)
            };
            node->child_to_parent.push_back(move(child_to_parent));
            node->children.push_back(build_node(move(child_newicks), int(side.size()), depth + 1));
        }
    }

    unique_ptr<Node> build_node(vector<string> newicks, int n, int depth) {
        auto node = make_unique<Node>();
        uint64_t local_seed = RANDOM_SEED ^
            (0x9e3779b97f4a7c15ULL + uint64_t(node_count) * 0xbf58476d1ce4e5b9ULL);
        node->solver = make_unique<AnnealSolver>(timer, local_seed);
        node->solver->load_instance(newicks, n);
        ++node_count;

        bool can_split = !timer.expired() &&
                         depth < CLUSTER_MAX_DEPTH &&
                         projected_blocks < CLUSTER_MAX_BLOCKS;
        if (can_split &&
            EARLY_SPLIT_CUTS > 0 &&
            EARLY_SPLIT_THRESHOLD > 0 &&
            node->solver->n > EARLY_SPLIT_THRESHOLD) {
            node->state = node->solver->start_search();
            node->state_started = node->state.initialized;
            if (node->state_started &&
                node->state.best.feasible &&
                node->state.best.components > EARLY_SPLIT_THRESHOLD) {
                AnnealSolver::MultiClusterSplit multi =
                    node->solver->find_multi_cluster_split(EARLY_SPLIT_CUTS);
                if (multi.found && can_add_split(int(multi.sides.size()))) {
                    ++split_count;
                    VERBOSE_CERR << "# early multi split depth " << depth
                         << " leaves " << node->solver->n
                         << " estimate " << node->state.best.components
                         << " cuts " << multi.nodes.size()
                         << " blocks " << multi.sides.size() << "\n";
                    split_node(node.get(), move(multi.sides), depth);
                    return node;
                }
            }
        }

        AnnealSolver::ClusterSplit split;
        if (can_split) split = node->solver->find_cluster_split();

        if (split.found && can_add_split(2)) {
            ++split_count;
            VERBOSE_CERR << "# cluster split depth " << depth
                 << " leaves " << node->solver->n
                 << " inside " << split.inside.size()
                 << " outside " << split.outside.size()
                 << " node " << split.node << "\n";

            vector<vector<int>> sides;
            sides.push_back(move(split.inside));
            sides.push_back(move(split.outside));
            split_node(node.get(), move(sides), depth);
        } else {
            leaves.push_back(node.get());
        }

        return node;
    }

    int choose_leaf() {
        int blocks = int(leaves.size());
        if (blocks <= 1) return 0;

        double total = 0.0;
        vector<double> weights(blocks, 1.0);
        for (int i = 0; i < blocks; ++i) {
            const Node* node = leaves[i];
            if (node->state_started) {
                weights[i] = max(1, node->state.cur.components);
            } else {
                weights[i] = double(max(1, node->solver->n));
            }
            total += weights[i];
        }

        double pick = rnd01() * total;
        for (int i = 0; i < blocks; ++i) {
            pick -= weights[i];
            if (pick <= 0.0) return i;
        }
        return blocks - 1;
    }

    void run_leaf_searches() {
        for (Node* leaf : leaves) {
            if (timer.expired()) break;
            if (!leaf->state_started) {
                leaf->state = leaf->solver->start_search();
                leaf->state_started = leaf->state.initialized;
            }
        }

        bool has_large_block = false;
        bool has_super_large_block = false;
        bool has_medium_super_large_block = false;
        for (Node* leaf : leaves) {
            if (leaf->state_started && leaf->solver->n > 5000) has_large_block = true;
            if (leaf->state_started && leaf->solver->n > 8000) has_super_large_block = true;
            if (leaf->state_started && leaf->solver->n > 8000 && leaf->solver->n <= 9000) {
                has_medium_super_large_block = true;
            }
        }

        double polish_budget = (!has_large_block || has_medium_super_large_block)
            ? min(POLISH_TIME_CAP, max(0.0, timer.limit_seconds * POLISH_TIME_FRAC))
            : 0.0;
        double global_merge_budget = min(CLUSTER_GLOBAL_MERGE_CAP,
                                         max(0.0, timer.limit_seconds * 0.05));
        double total_sa_end = timer.limit_seconds - polish_budget - global_merge_budget;
        bool has_very_large_block = false;
        bool has_only_small_blocks = true;
        bool has_only_very_small_blocks = true;
        for (Node* leaf : leaves) {
            if (leaf->state_started && leaf->solver->n > 7500) has_very_large_block = true;
            if (leaf->state_started && leaf->solver->n >= 300) has_only_small_blocks = false;
            if (leaf->state_started && leaf->solver->n >= 200) has_only_very_small_blocks = false;
        }

        bool has_very_large_only = has_very_large_block && !has_super_large_block;
        int total_rounds = max(1, 1 + NUM_RESTARTS +
            (has_very_large_block ? 1 : 0) +
            (has_super_large_block ? 1 : 0) +
            (has_very_large_only ? 2 : 0) +
            (has_medium_super_large_block ? 1 : 0) +
            (has_only_small_blocks ? 3 : 0) +
            (has_only_very_small_blocks ? 3 : 0));
        if (has_medium_super_large_block && polish_budget > 0.0) total_rounds = min(total_rounds, 3);

        double sa_start_time = timer.elapsed();
        double per_round = max(0.1, (total_sa_end - sa_start_time) / total_rounds);
        long long total_iterations = 0;

        for (int round = 0; round < total_rounds; ++round) {
            double round_stop = min(sa_start_time + per_round * (round + 1), total_sa_end);
            if (timer.expired() || timer.elapsed() >= round_stop) break;

            if (round == 0) {
                for (Node* leaf : leaves) {
                    if (!leaf->state_started) continue;
                    if (NUM_RESTARTS > 0 &&
                        ((leaf->solver->n >= RESTART_MIN_N) ||
                         (leaf->solver->n >= 50 && leaf->solver->n < RESTART_MIN_N))) {
                        leaf->state.anneal_stop_time = min(leaf->state.anneal_stop_time, round_stop);
                        leaf->state.anneal_budget = max(0.001,
                            leaf->state.anneal_stop_time - leaf->state.anneal_start);
                    }
                }
            } else {
                for (Node* leaf : leaves) {
                    if (!leaf->state_started || timer.expired()) continue;
                    if (leaf->solver->n < RESTART_MIN_N && leaf->solver->n < 50) {
                        leaf->state.anneal_stop_time = max(leaf->state.anneal_stop_time, round_stop);
                        leaf->state.anneal_budget = max(0.001,
                            leaf->state.anneal_stop_time - leaf->state.anneal_start);
                        continue;
                    }

                    AnnealEval prev_best = leaf->state.best;
                    vector<unsigned char> prev_best_cut = leaf->state.best_cut;
                    vector<unsigned char> next_cut;
                    leaf->solver->rng ^= 0x9e3779b97f4a7c15ULL * uint64_t(round);
                    next_cut = prev_best_cut;
                    double perturb_frac;
                    if (leaf->solver->n > 9000 && has_super_large_block) {
                        perturb_frac = 0.04 * pow(0.5, round - 1);
                    } else if (leaf->solver->n > 8000 && has_medium_super_large_block) {
                        perturb_frac = 0.05;
                    } else if (leaf->solver->n > 7000 && leaf->solver->n <= 7500) {
                        perturb_frac = 0.05 * pow(0.6, round - 1);
                    } else if (leaf->solver->n < RESTART_MIN_N) {
                        perturb_frac = (leaf->solver->n < 200) ? 0.05 : 0.10;
                    } else if (leaf->solver->n < 2500) {
                        perturb_frac = 0.02;
                    } else {
                        perturb_frac = RESTART_PERTURB_FRAC;
                    }
                    int flip_count = (leaf->solver->n < RESTART_MIN_N)
                        ? max(2, int(perturb_frac * leaf->solver->nonroot_edges.size()))
                        : max(5, int(perturb_frac * leaf->solver->nonroot_edges.size()));
                    leaf->solver->perturb_cut(next_cut, flip_count);

                    leaf->state = leaf->solver->restart_search_from_cut(
                        next_cut, prev_best, prev_best_cut, round_stop);
                    leaf->state_started = leaf->state.initialized;
                }
            }

            while (!timer.expired() && timer.elapsed() < round_stop && !leaves.empty()) {
                int idx = choose_leaf();
                Node* leaf = leaves[idx];
                if (!leaf->state_started) continue;
                if (leaf->solver->anneal_step(leaf->state)) ++total_iterations;
            }
        }

        VERBOSE_CERR << "# cluster search blocks " << leaves.size()
             << " splits " << split_count
             << " rounds " << total_rounds
             << " interleaved_iterations " << total_iterations << "\n";

        vector<Node*> order = leaves;
        sort(order.begin(), order.end(), [](const Node* a, const Node* b) {
            int ca = a->state_started ? a->state.best.components : a->solver->n;
            int cb = b->state_started ? b->state.best.components : b->solver->n;
            return ca > cb;
        });
        double block_polish_stop = max(timer.elapsed(), timer.limit_seconds - CLUSTER_GLOBAL_MERGE_CAP);
        int active_count = 0;
        for (Node* leaf : order) {
            if (leaf->state_started) ++active_count;
        }
        for (Node* leaf : order) {
            if (timer.expired()) break;
            if (timer.elapsed() >= block_polish_stop) break;
            if (!leaf->state_started) continue;
            double remaining = block_polish_stop - timer.elapsed();
            double block_stop = (remaining >= 0.0 && active_count > 0)
                                ? min(block_polish_stop, timer.elapsed() + remaining / active_count)
                                : block_polish_stop;
            leaf->solver->finish_search(leaf->state, block_stop);
            --active_count;
        }
    }

    vector<string> collect_lines(Node* node) {
        if (node->children.empty()) {
            vector<Component> comps = node->state_started
                                      ? node->solver->components_from_search(node->state)
                                      : node->solver->singleton_solution();
            return node->solver->solution_lines(comps);
        }

        vector<string> mapped_lines;
        for (int i = 0; i < int(node->children.size()); ++i) {
            vector<string> child_lines = collect_lines(node->children[i].get());
            for (const string& line : child_lines) {
                mapped_lines.push_back(relabel_newick(line, node->child_to_parent[i]));
            }
        }

        if (node->solver->reductions.active) {
            vector<Component> comps = components_from_newick_lines(mapped_lines);
            vector<string> expanded = node->solver->reductions.expand_to_newicks(comps);
            if (!expanded.empty()) return expanded;
        }
        return mapped_lines;
    }

    vector<string> global_merge_polish(const vector<string>& lines,
                                       const vector<string>& original_newicks,
                                       int original_n) {
        if (CLUSTER_GLOBAL_MERGE_CAP <= 0.0 || timer.expired() ||
            original_newicks.size() != 2 || lines.empty()) {
            return lines;
        }

        double remaining = timer.limit_seconds - timer.elapsed();
        double cap = min(CLUSTER_GLOBAL_MERGE_CAP, remaining - 0.05);
        if (cap <= 0.02) return lines;

        Timer polish_timer(cap);
        GreedyMergeSolver helper(polish_timer);
        helper.n = original_n;
        helper.interner.reset(original_n);
        helper.trees[0] = Tree::parse_newick(original_newicks[0], original_n);
        helper.trees[1] = Tree::parse_newick(original_newicks[1], original_n);
        helper.trees[0].preprocess(helper.interner);
        helper.trees[1].preprocess(helper.interner);

        vector<Component> comps;
        comps.reserve(lines.size());
        for (const string& line : lines) {
            Component c;
            c.labels = labels_from_newick(line);
            if (c.labels.empty()) continue;
            c.tin_labels[0] = helper.trees[0].labels_by_tin(c.labels);
            c.tin_labels[1] = helper.trees[1].labels_by_tin(c.labels);
            Tree::Analysis a0 = helper.trees[0].analyze_sorted_labels(c.tin_labels[0],
                                                                       helper.interner, true);
            Tree::Analysis a1 = helper.trees[1].analyze_sorted_labels(c.tin_labels[1],
                                                                       helper.interner, true);
            if (a0.id != a1.id) return lines;
            c.id = a0.id;
            c.edges[0] = move(a0.edges);
            c.edges[1] = move(a1.edges);
            comps.push_back(move(c));
        }
        if (comps.empty()) return lines;

        int before = int(comps.size());
        GreedyMergeSolver::Forest f = helper.make_forest(move(comps));
        helper.improve(f);
        int split_merge_improvements = 0;
        if (!polish_timer.expired()) {
            split_merge_improvements = helper.split_merge_polish(f);
        }
        vector<Component> improved = helper.active_components(f);
        if (int(improved.size()) > before) return lines;

        vector<string> out;
        out.reserve(improved.size());
        for (const Component& c : improved) out.push_back(helper.interner.to_newick(c.id));
        VERBOSE_CERR << "# cluster global_merge before " << before
             << " after " << out.size()
             << " split_merge " << split_merge_improvements
             << " cap " << cap << "\n";
        return out;
    }

    vector<string> solve(vector<string> newicks, int n) {
        vector<string> original_newicks = newicks;
        unique_ptr<Node> root = build_node(move(newicks), n, 0);
        run_leaf_searches();
        vector<string> lines = collect_lines(root.get());
        lines = global_merge_polish(lines, original_newicks, n);
        sort(lines.begin(), lines.end(), [](const string& a, const string& b) {
            vector<int> la = labels_from_newick(a);
            vector<int> lb = labels_from_newick(b);
            int fa = la.empty() ? 0 : la.front();
            int fb = lb.empty() ? 0 : lb.front();
            return fa < fb;
        });
        return lines;
    }
};

int main(int argc, char** argv) {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    signal(SIGTERM, handle_signal);
    signal(SIGINT, handle_signal);

    Timer timer(read_time_limit(argc, argv));
    RawInput input = read_raw_input();

    ClusterManager manager(timer);
    vector<string> lines = manager.solve(move(input.newicks), input.n);
    for (const string& line : lines) cout << line << ";\n";
    
    return 0;
}
