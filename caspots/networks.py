
import itertools as it

import clingo

import pandas as pd

from caspo.core import Clause

from .asputils import *


def network_str(network):
    def clause_str(c):
        if len(c) == 0:
            return "FALSE"
        return " OR ".join(["+".join(map(str, ls)) for ls in c])
    return " / ".join(["%s = %s" % (v,clause_str(c)) for v,c in network.formulas_iter()])


def domain_of_networks(networks):

    hg = networks.hg

    domain = ["1{%s}1." % ("; ".join(["model(%d)" % i for i in range(len(networks))]))]

    for i,network in enumerate(networks):
        m = clingo.Function("model", [i])
        for v,formula in network.formulas_iter():
            variable = hg.nodes[hg.nodes == v].index[0]
            f = clingo.Function("formula", [v, variable])
            domain.append("%s :- model(%d)." % (f,i))
            for clause in formula:
                clause_idx = hg.clauses_idx[clause]
                d = clingo.Function("dnf",[variable, clause_idx])
                domain.append("%s :- %s." % (d,m))
                for variable, sign in clause:
                    c = clingo.Function("clause", [clause_idx, variable, sign])
                    domain.append("%s :- %s." % (c,m))

    return "%s\n" % "\n".join(domain)

def restrict_with_partial_bn(hypergraph, partial_bn_file):
    asp = []

    def parse_clause(data):
        data = data.strip()
        complete = True
        if data.endswith(".."):
            data = data.strip(".")
            complete = False
        return Clause.from_str(data), complete


    with open(partial_bn_file) as f:
        for line in f:
            line = line.strip().replace(' ','')
            if not line:
                continue
            a, clauses = line.split("=")
            a = a.strip()
            ai = hypergraph.nodes[hypergraph.nodes == a].index[0]
            clauses = dict([parse_clause(c) for c in clauses.split("|")])
            partial_req = {}

            def register_surclause(c, hi):
                if c not in partial_req:
                    partial_req[c] = []
                partial_req[c].append(hi)

            for hi in hypergraph.hyper[hypergraph.hyper == ai].index:
                hc = hypergraph.clauses[hi]
                complete = clauses.get(hc)
                if complete:
                    asp.append("dnf({0},{1}).".format(ai, hi))
                elif complete is None:
                    has_subset = False
                    for c, complete in clauses.items():
                        if not complete and c.issubset(hc):
                            has_subset = True
                            register_surclause(c, hi)
                    if not has_subset:
                        asp.append(":- dnf({0},{1}).".format(ai,hi))
                else:
                    register_surclause(hc, hi)

            for his in partial_req.values():
                asp.append("1 {%s}." % ";".join(["dnf({},{})".format(ai,hi) for hi in his]))

    return "\n".join(asp)
