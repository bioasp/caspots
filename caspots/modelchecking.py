#!/usr/bin/env python

import subprocess

from .utils import *

U_GENERAL = "general"
U_ASYNC = "asynchronous"

MODES = [U_GENERAL, U_ASYNC]

def make_smv(dataset, network, destfile, update=U_GENERAL):

    # nodes referenced in dataset
    dvars = dataset.setup.nodes.union(network.variables())

    control_nodes = dataset.control_nodes

    # nodes for which a function is defined
    varying_nodes = set([node for node, _ in network.formulas_iter()])
    varying_nodes.update(control_nodes)

    # nodes with no function (i.e., constant value)
    constants = dvars.difference(varying_nodes)
    #constants = dataset.stimulus.difference(varying_nodes)

    dirty_start = set()
    for exp in dataset.experiments.values():
        if 0 not in exp.obs:
            dirty_start.update(dataset.readout)
            break
        else:
            readouts0 = set(exp.obs[0].keys())
            dirty_start.update(dataset.readout.difference(readouts0))

    clampable = varying_nodes.intersection(dataset.inhibitors.union(dataset.stimulus))
    assert not control_nodes.intersection(clampable), "Control nodes should not be declared as TR!"

    smv = open(destfile, "w")
    smv.write("MODULE main\n")
    smv.write("\nVAR\n")
    smv.write("\tstart: boolean;\n")
    for n in constants:
        smv.write("\tn_%s: boolean;\n" % n)
    for n in varying_nodes:
        smv.write("\tn_%s: boolean;\n" % n)
        smv.write("\tu_%s: boolean;\n" % n)
        if n in clampable:
            smv.write("\tC_%s: {0,1,-1};\n" % n)
    for n in dirty_start:
        smv.write("\tdirty_%s: boolean;\n" % n)

    smv.write("\nASSIGN\n")
    smv.write("next(start) := FALSE;\n")
    for n in dirty_start:
        smv.write("next(dirty_%s) := FALSE;\n" % n)
    for n in constants:
        smv.write("next(n_%s) := n_%s;\n" % (n,n))
    for n in varying_nodes:
        smv.write("next(n_%s) := case " % n)
        if n not in dataset.readout:
            smv.write("start: {TRUE, FALSE}; ")
        elif n in dirty_start:
            smv.write("start & dirty_%s: {TRUE, FALSE}; " % n)
        smv.write("u_%s: F_%s; TRUE: n_%s; esac;\n" % (n, n, n))
        if n in clampable:
            smv.write("next(C_%s) := C_%s;\n" % (n, n))
        #smv.write("next(u_%s) := {TRUE, FALSE};\n" % n)

    smv.write("\nDEFINE\n")

    def nusmv_of_literal(vs):
        (var, sign) = vs
        return "%sn_%s" % ("!" if sign <= 0 else "", var)

    def nusmv_of_clause(clause):
        expr = " & ".join(map(nusmv_of_literal, clause))
        if len(clause) > 1:
            return "(%s)" % expr
        return expr

    def nusmv_of_clauses(clauses):
        if len(clauses) == 0:
            return "FALSE"
        return " | ".join(map(nusmv_of_clause, clauses))

    for n, clauses in network.formulas_iter():
        if n in control_nodes:
            continue
        expr = nusmv_of_clauses(clauses)
        if n in clampable:
            smv.write("F_%s := case C_%s=0: %s; " % (n, n, expr))
            smv.write("C_%s=1: TRUE; C_%s=-1: FALSE; esac;\n" % (n, n))
        else:
            smv.write("F_%s := %s;\n" % (n, expr))
    for n in control_nodes:
        smv.write("F_{0} := !n_{0};\n".format(n))

    for exp in dataset.experiments.values():
        setup = []
        # enforce initial state of clamped nodes
        for (n, c) in exp.mutations.items():
            setup.append("%sn_%s" % ("!" if c < 0 else "", n))
        # specify clamping setting
        for n in clampable:
            if n in exp.mutations:
                c = exp.mutations[n]
                setup.append("C_%s=%s" % (n,c))
            else:
                setup.append("C_%s=0" % n)

        smv.write("E%d_SETUP := %s;\n" % (exp.id, " & ".join(setup) or "TRUE"))
        if 0 not in exp.obs:
            smv.write("E%d_T0 := %s;\n" % (exp.id,
                " & ".join(["dirty_%s" % n for n in dirty_start])))
        for t, values in exp.obs.items():
            state = []
            for n, v in values.items():
                state.append("%sn_%s" % ("!" if not v else "", n))
            if t == 0:
                for n in dirty_start:
                    neg = "!" if n not in values else ""
                    state.append("%sdirty_%s" % (neg, n))
            smv.write("E%d_T%d := %s;\n" % (exp.id, t, " & ".join(state)))

    fpconds = ["n_%s = F_%s" % (n, n) for n in varying_nodes]
    smv.write("FIXEDPOINTS := %s;\n" % " & ".join(fpconds))

    smv.write("\nTRANS\n")
    smv.write("  next(start) != start")
    for n in varying_nodes:
        smv.write("\n| next(n_%s) != n_%s" % (n,n))
        smv.write("\n| next(u_%s) != u_%s" % (n,n))
    smv.write("\n| FIXEDPOINTS")
    smv.write(";\n")

    if update == U_ASYNC:
        for n in varying_nodes:
            cond = " & ".join(["!u_%s" % m for m in varying_nodes if m != n])
            smv.write("TRANS u_%s -> %s;\n" % (n, cond))

    smv.write("\nINIT\n")
    smv.write("(start")
    for n in varying_nodes:
        smv.write(" & !u_%s" % n)
    smv.write(");\n")

    if update == U_ASYNC:
        control_stages = async_interleavings
    else:
        control_stages = general_interleavings

    def ctl_of_exp(exp):
        def control_state(t):
            return dict([(n,v) for (n,v) in exp.obs[t].items() if n in control_nodes])

        def ctl_of_timeseries(t, ts):
            if not ts:
                return "TRUE"

            ctl_t = "E{exp}_T{t}".format(exp=exp.id, t=ts[0])
            if len(ts) == 1:
                next_ctl = ctl_t
            else:
                next_ctl = "({} & {})".format(ctl_t, ctl_of_timeseries(ts[0], ts[1:]))

            if not control_nodes:
                return "EF {}".format(next_ctl)

            begin_control_state = control_state(t)
            next_control_state = control_state(ts[0])

            for n in control_nodes:
                assert n in begin_control_state, \
                    "Exp {}: {} is not defined at t={}".format(exp.id, n, t)
                assert n in next_control_state, \
                    "Exp {}: {} is not defined at t={}".format(exp.id, n, ts[0])

            changing_control = [n for n in control_nodes \
                        if begin_control_state[n] != next_control_state[n]]

            control_paths = []
            for stages in control_stages(changing_control):
                cur_control_state = begin_control_state.copy()
                control_path = [nusmv_of_clause(cur_control_state.items())]
                for stage in stages:
                    for n in stage:
                        cur_control_state[n] = next_control_state[n]
                    if stage:
                        control_path.append(nusmv_of_clause(cur_control_state.items()))
                control_paths.append(control_path)

            def ctl_of_control_path(control_path):
                ctl_path = ""
                nb_par = 0
                for steady in control_path:
                    ctl_path += "E [{} U ".format(steady)
                    nb_par += 1
                ctl_path += next_ctl
                ctl_path += "]"*nb_par
                return "({})".format(ctl_path)

            ctl = "|".join(map(ctl_of_control_path, control_paths))
            if len(control_paths) > 1:
                ctl = "({})".format(ctl)
            return ctl

        ts = list(sorted(exp.obs.keys()))
        if ts[0] == 0:
            ts.pop(0)
        ctl = ctl_of_timeseries(0, ts)

        return "((E{exp}_SETUP & E{exp}_T0) -> {ctl})"\
                .format(exp=exp.id, ctl=ctl)

    smv.write("CTLSPEC ")
    smv.write("\n & ".join([ctl_of_exp(exp) for exp in dataset.experiments.values()]))
    smv.write("\n")

    smv.close()
    return destfile

def verify(dataset, network, destfile, *args, **kwargs):
    smvfile = make_smv(dataset, network, destfile, *args, **kwargs)
    output = subprocess.check_output(["NuSMV", "-coi", "-dcx", smvfile])
    ret = output.strip().split()[-1].decode()
    return ret == "true"

