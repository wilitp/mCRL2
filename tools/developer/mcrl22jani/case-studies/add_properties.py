#!/usr/bin/env python3
"""Post-process a self_stabilisation JANI produced by mcrl22jani so it can be
model-checked in the Modest Toolset (mcsta).

mcrl22jani emits no JANI `properties`, and Modest cannot reference an automaton's
*local* variables in a property.  This script therefore does two things:

  1. Promotes each automaton's local `Pi_token` bool to a GLOBAL variable with
     initial value `true` (the real initial configuration: every process holds a
     token).  This is an observation-only transform: each `Pi_token` is written
     only by its own automaton, so making it global does not change behaviour.
  2. Injects the five properties evaluated in the case study, over
     `#tokens = sum_i (Pi_token ? 1 : 0)` and `stable = (#tokens = 1)`.

Step convention (important for reading P4/P5): each property accumulates the
built-in `steps` reward with instantaneous value 1, i.e. it counts ONE per JANI
transition fired until `stable` first holds.  That count INCLUDES the one-off
`INIT --init--> body` Stoch-resolution edge (verified empirically: expected
transitions to the first token merge = 2 = init edge + 1 merge).  So every
expected-time figure carries a constant +1 relative to a model with no initial
distribution edge.

Usage:  python3 add_properties.py self_stabilisation.jani self_stabilisation.checked.jani
"""
import json
import sys


def main(src, dst):
    m = json.load(open(src))

    # 1. promote every Pi_token to a global bool, initial value true
    tokens = []
    for a in m["automata"]:
        keep = []
        for v in a.get("variables", []):
            if v["name"].endswith("_token"):
                m["variables"].append(
                    {"name": v["name"], "type": "bool",
                     "initial-value": True, "transient": False})
                tokens.append(v["name"])
            else:
                keep.append(v)
        a["variables"] = keep
    n = len(tokens)

    # #tokens  and  stable = (#tokens = 1)
    def ite(t):
        return {"op": "ite", "if": t, "then": 1, "else": 0}

    ntok = ite(tokens[0])
    for t in tokens[1:]:
        ntok = {"op": "+", "left": ntok, "right": ite(t)}
    stable = {"op": "=", "left": ntok, "right": 1}

    def reach_prob(op, name, target):
        return {"name": name, "expression": {
            "op": "filter", "fun": ("max" if op == "Pmax" else "min"),
            "states": {"op": "initial"},
            "values": {"op": op, "exp": {"op": "U", "left": True, "right": target}}}}

    def exp_steps(op, name, target):
        return {"name": name, "expression": {
            "op": "filter", "fun": ("max" if op == "Emax" else "min"),
            "states": {"op": "initial"},
            "values": {"op": op, "exp": 1, "accumulate": ["steps"], "reach": target}}}

    vanish = {"op": "=", "left": ntok, "right": 0}          # tokens ever vanish
    grow = {"op": ">", "left": ntok, "right": n}            # tokens ever exceed N
    m["properties"] = [
        reach_prob("Pmax", "P1_tokens_vanish", vanish),     # expect 0
        reach_prob("Pmax", "P2_tokens_grow", grow),         # expect 0
        reach_prob("Pmin", "P3_self_stabilises", stable),   # expect 1 (exactly)
        exp_steps("Emax", "P4_exp_steps_max", stable),      # worst-case expected steps
        exp_steps("Emin", "P5_exp_steps_min", stable),      # best-case expected steps
    ]

    json.dump(m, open(dst, "w"), indent=1)
    print(f"wrote {dst}: {n} processes, tokens={tokens}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
