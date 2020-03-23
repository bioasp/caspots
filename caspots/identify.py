
from __future__ import print_function

import math
import os
from subprocess import *
import sys
import tempfile
import time

import gringo

from caspo.core import LogicalNetwork

from caspots.config import *
from caspots import asputils
from caspots.utils import *

def crunch_data(answer, predicate, factor):
    factor = float(factor)
    data = {
        "obs": {},
        "bin": {}
    }
    keys = set()
    for a in answer:
        p = a.name()
        if p in ["obs", predicate]:
            args = a.args()
            key = tuple(args[:3])
            val = args[3]
            if p == "obs":
                val /= factor
            t = "obs" if p == "obs" else "bin"
            data[t][key] = val
            keys.add(key)
    return (keys, data)

def MSE(cd):
    cum = 0
    keys, data = cd
    n = 0
    for key in keys:
        if key not in data["obs"]:
            continue
        if key not in data["bin"]:
            continue
        n += 1
        cum += (data["obs"][key] - data["bin"][key])**2
    return math.sqrt(cum/n)

def count_predicate(answer, predicate):
    return len([a for a in answer if a.name() == predicate])

class ASPSample:
    def __init__(self, opts, model):
        self.opts = opts
        self.atoms = model.atoms()
        self.optimization = model.optimization()

    def weight(self):
        return self.optimization[0]

    def size(self):
        return self.optimization[1] if len(self.optimization) > 1 else None

    def asp_exclusion(self):
        predicates = ["formula", "dnf", "clause"]
        if self.opts.enum_traces:
            predicates += ["guessed"]
        clauses = [a for a in self.atoms if a.name() in predicates]
        if self.opts.family == "all":
            nb_formula = count_predicate(self.atoms, "formula")
            nb_dnf = count_predicate(self.atoms, "dnf")
            nb_clause = count_predicate(self.atoms, "clause")
            clauses += [
                "%d{formula(V,I): node(V,I)}%d" % (nb_formula, nb_formula),
                "%d{dnf(I,J): hyper(I,J,N)}%d" % (nb_dnf, nb_dnf),
                "%d{clause(J,V,B): edge(J,V,B)}%d" % (nb_clause, nb_clause)
            ]
        return ":- %s." % ", ".join(map(str, clauses))

    def mse(self):
        cd_measured = crunch_data(self.atoms, "measured", self.opts.factor)
        cd_guessed = crunch_data(self.atoms, "guessed", self.opts.factor)
        mse0 = MSE(cd_measured)
        mse = MSE(cd_guessed)
        return (mse0, mse)

    def network(self, hypergraph):
        tuples = (f.args() for f in self.atoms if f.name() == "dnf")
        return LogicalNetwork.from_hypertuples(hypergraph, tuples)

    def trace(self, dataset):
        # rewrite dataset using guessed predicate
        for a in self.atoms:
            if a.name() == "guessed":
                eid, t, node, value = a.args()
                if node not in dataset.readout:
                    continue
                if node in dataset.control_nodes:
                    continue
                if node not in dataset.experiments[eid].obs[t]:
                    continue
                if dataset.experiments[eid].obs[t][node] != value:
                    #print(((eid,t,node),dataset.experiments[eid].obs[t][node], value), file=sys.stderr)
                    dataset.experiments[eid].obs[t][node] = value
        return dataset

def print_conf(conf, prefix=""):
    for k in conf.keys():
        v = getattr(conf, k)
        if isinstance(v, gringo.ConfigProxy):
            print_conf(v, "%s%s" % (prefix, k))
        else:
            dbg("# conf %s%s = %s" % (prefix, k, v))

class ASPSolver:
    def __init__(self, termset, opts, domain=None, restrict=None,
                        fixpoints=False, nodataset=False):
        self.termset = termset
        self.data = termset.to_str()
        self.opts = opts
        self.debug = opts.debug
        self.nodataset = nodataset
        if domain is None:
            self.domain = [aspf("guessBN.lp")]
            if opts.fully_controllable:
                self.domain.append(aspf("guessBN-controllable.lp"))
            if restrict:
                self.domain.append(restrict)
        else:
            self.domain = [domain]
        if fixpoints:
            self.domain.append(aspf("fixpoints.lp"))

    def default_control(self, *args):
        control = gringo.Control(["--conf=trendy", "--stats",
                            "--opt-strat=usc"] + list(args))
        for f in self.domain:
            control.load(f)
        if not self.nodataset:
            control.load(aspf("supportConsistency.lp"))
            control.load(aspf("normalize.lp"))
        control.add("base", [], self.data)

        if self.opts.clingo_parallel_mode:
            control.conf.solve.parallel_mode = self.opts.clingo_parallel_mode

        return control

    def sample(self, control, first, weight=None, minsize=None):
        if first:
            #control.conf.solve.opt_mode = "opt"
            self.setup_opt(control)

            control.ground([("base", [])])

            control.load(aspf("show.lp"))
            control.ground([("show", [])])
            control.assign_external(gringo.Fun("tolerance"),False)

        else:
            if weight:
                self.setup_weight(control, weight)
            if minsize:
                self.setup_card(control, minsize)
            control.conf.solve.opt_mode = "ignore"
            control.conf.solve.models = 1

        models = []
        res = control.solve(None, lambda model: models.append(ASPSample(self.opts, model)))
        if models:
            model = models.pop()
            return model

    def solution_samples(self):
        control = self.default_control()
        weight = None
        size = None
        i = 0
        while True:
            s = self.sample(control, i == 0, weight=weight, minsize=size)
            if s:
                i += 1
                yield s
                if i == 1:
                    weight = s.weight()
                    size = s.size()
                    dbg("# first sample weight = %s, size = %s" % (weight, size))
                control.add("excl", [], s.asp_exclusion())
                control.ground([("excl", [])])
            else:
                print("# Enumeration complete")
                break

    def setup_opt(self, control):
        control.load(aspf("minimizeWeightOnly.lp"))
        if self.do_mincard:
            control.load(aspf("minimizeSizeOnly.lp"))

    def setup_weight(self, control, weight):
        max_weight = weight + self.opts.weight_tolerance
        control.add("minWeight", [], ":- not " + str(weight) + " #sum {Erg,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=50-M, M < 50;" + " Erg,E,T,S : measured(E,T,S,V), not guessed(E,T,S,V), toGuess(E,T,S), obs(E,T,S,M), Erg=M-49, M >= 50} " + str(max_weight) + " .")
        control.ground([("minWeight", [])])

    def setup_card(self, control, minsize):
        if self.do_mincard:
            if self.opts.force_size:
                maxsize = self.opts.force_size
            else:
                maxsize = minsize + self.opts.mincard_tolerance
            control.add("minSize", [], ":- not " + str(minsize) + " #sum {L,I,J : dnf(I,J) , hyper(I,J,L)} " + str(maxsize) + ".")
            control.ground([("minSize", [])])

    @property
    def do_mincard(self):
        return  self.opts.family == "mincard" \
            or self.opts.force_size is not None

    def solutions(self, on_model, on_model_weight=None, limit=0,
                    force_weight=None):

        control = self.default_control("0")

        do_subsets = self.opts.family == "subset" \
            or (self.opts.family =="mincard" and self.opts.mincard_tolerance)
        minsize = None

        self.setup_opt(control)
        control.ground([("base", [])])

        control.load(aspf("show.lp"))
        control.ground([("show", [])])

        start = time.time()

        if self.nodataset:
            force_weight = 0

        if force_weight is None:
            control.assign_external(gringo.Fun("tolerance"),False)
            dbg("# start initial solving")
            opt = []
            res = control.solve(None, lambda model: opt.append(model.optimization()))
            dbg("# initial solve took %s" % (time.time()-start))

            optimizations = opt.pop()
            dbg("# optimizations = %s" % optimizations)

            weight = optimizations[0]
            if self.do_mincard:
                minsize = optimizations[1]
            if weight > 0 and on_model_weight is not None:
                dbg("# model has weight, changing enumeration mode")
                for sample in self.solution_samples():
                    on_model_weight(sample)
                return

            control.assign_external(gringo.Fun("tolerance"),True)
        else:
            weight = force_weight
            control.assign_external(gringo.Fun("tolerance"),True)
            dbg("# force weight = %d" % weight)

        self.setup_weight(control, weight)
        self.setup_card(control, minsize)

        control.conf.solve.opt_mode = "ignore"
        control.conf.solve.project = 1 # ????
        control.conf.solve.models = limit # ????
        #print control.conf.solver[0].keys()
        if do_subsets:
            control.conf.solve.enum_mode = "domRec"
            control.conf.solver[0].heuristic = "Domain"
            control.conf.solver[0].dom_mod = "5,16"

        start = time.time()
        dbg("# begin enumeration")
        res = control.solve(None, on_model)
        dbg("# enumeration took %s" % (time.time()-start))


