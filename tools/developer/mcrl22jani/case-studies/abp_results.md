# ABP case study — evaluation results

Evaluation of the `mcrl22jani` translation on the **Alternating Bit Protocol (ABP)**,
the classic (non-probabilistic) case study. The goal is *translation validation*: we
translate the mCRL2 spec to JANI, load the JANI into an independent model checker
(the **Modest Toolset**, `mcsta`), and check that the result reproduces ABP's known
behaviour. This is a differential check — the reference is the well-understood
semantics of ABP, not `mcrl22jani` itself.

## Model under test

- **Spec:** [`abp_closed.mcrl2`](./abp_closed.mcrl2), adapted from
  `examples/academic/abp/abp.mcrl2`.
- **Adaptations** (each illustrates a subset boundary; see the spec header):
  1. data domain `D` → `Bool` (finite);
  2. receiver reads the bit into a **bare** sum variable and guards on it
     (`sum d,cb:Bool. r3(d,cb).((cb==b) -> …)`);
  3. the open upper-layer input is **closed** with a `Source` process, since a lone
     external read has no writer;
  4. lossy channels deliver **either the frame or a nullary corrupted-frame signal**
     (`s3e` / `s6e`), never a silent drop — mirroring the upstream error token
     `s3(e)` / `s6(e)`. This preserves ABP's liveness (see "deadlock-freedom" below).
- **Composition:** `Source ‖ S ‖ K ‖ L ‖ R` → 5 JANI automata (system-element order
  `[Source, S, K, L, R]`). Channels `K` and `L` corrupt *nondeterministically*.
- **Type:** JANI `mdp`. Note ABP has **no probabilistic choice** (`dist`), so the
  model is a purely *nondeterministic* MDP; every `Pmin`/`Pmax` below is therefore
  qualitative (`0` or `1`), i.e. "for all / there exists a scheduler".

## Toolchain

| Component | Version / ref |
|---|---|
| `mcrl22jani` | this repo, branch `mcrl22jani`, translator at commit `f921327d39` |
| Modest Toolset (`mcsta`) | `v3.1.301-gfcaf4299f` |

```
build/stage/bin/mcrl22jani < abp_closed.mcrl2 > abp.jani     # translate
modest check abp.jani                                        # model-check (mcsta)
modest check --nofixdl abp.jani                              # + report deadlock states
```

`mcrl22jani` does not yet emit JANI `properties`, so each property below was injected
into the JANI. Delivery is observed with a **non-transient global flag** `delivered`,
set to `true` on the receiver's `s4` (deliver) edge; `s4_1` is the record variable
holding the value the receiver delivered.

**`--nofixdl` matters.** By default `mcsta` makes the MDP total by adding a self-loop to
every deadlock (sink) state, so genuine deadlocks are silently masked. `--nofixdl`
disables that and makes `mcsta` report any reachable deadlock — this is how P4 is
checked (there is no supported `deadlock` *property* in this build).

## Properties checked

| # | Meaning | Formal (from initial state) | Result | Expected |
|---|---|---|---|---|
| P1 | delivery is **possible** (some scheduler delivers) | `Pmax(◇ delivered)` | **1** | 1 |
| P2 | delivery is **guaranteed** (every scheduler delivers) | `Pmin(◇ delivered)` | **0** | 0 |
| P3 | **data fidelity**: a `true` datum reaches the receiver | `Pmax(◇ s4_1 = true)` | **1** | 1 |
| P4 | **deadlock-freedom** | `mcsta --nofixdl`: no reachable deadlock | **holds** | holds |

State space (fully explored by `mcsta`): **26 states / 31 transitions** for P1/P2/P4;
**77 / 96** when the datum value is made observable (P3).

## Reference values and their source

**Reference:** J.F. Groote and M.R. Mousavi, *Modeling and Analysis of Communicating
Systems*, The MIT Press, 2014 — the source of the original `abp.mcrl2` model (cited in
its header). ABP's correctness result there: after hiding the internal actions and
reducing modulo **branching bisimulation**, ABP is equivalent to a **one-place buffer**
— a deadlock-free process that reliably delivers each datum in order, **provided the
channels do not corrupt/lose messages infinitely often** (a fairness / progress
assumption, classically handled by *fair abstraction* / Koomen's Fair Abstraction Rule).

Mapping that reference onto our unfair MDP (corruption = nondeterminism, no fairness):

- **P1 = 1** — a cooperative scheduler (channels eventually forward) delivers, so a
  delivering run exists. Matches "ABP delivers under fair channels."
- **P2 = 0** — an adversarial scheduler that *always* corrupts prevents delivery forever.
  Matches the reference's fairness caveat: without a progress assumption on the channels,
  ABP guarantees nothing. This 0/1 gap between `Pmax` and `Pmin` is exactly the expected
  signature of unreliable-but-unfair channels.
- **P3 = 1** — the datum's value (not just "some delivery") is transmitted faithfully:
  the bit *and* the data reach the receiver and the guard matches. Confirms the
  value-passing translation is semantically correct end-to-end.
- **P4 holds** — the one-place-buffer reference is deadlock-free, and so is the model:
  the corrupted-frame signal always keeps a message in flight, so the sender can always
  eventually retransmit and no global state gets stuck.

All four match the expected behaviour.

## What the evaluation surfaced

Running the JANI in Modest was worthwhile beyond confirming the expected values — it
caught **two real translation bugs** (both now fixed on this branch) and **one modelling
error** that translating-and-eyeballing had missed:

1. **Sync-column ordering** (translator bug, fixed in `58f0516abf`). Parallel operands
   were collected into a `multiset`, which reorders by term value, while sync-vector
   columns follow the syntactic `merge` order. The two disagreed for
   `Source ‖ S ‖ K ‖ L ‖ R`, so every communication sync referenced the wrong automaton
   and the model **deadlocked after the initial step** — `mcsta` reported only 2 states.
   Fixed → the composition explores fully.
2. **Process-instance parameter capture** (translator bug, fixed in `f921327d39`). The
   call `T(d,b)` inside `S(b)=sum d. …T(d,b)` emitted the self-assignments `T_d:=T_d`,
   `T_b:=T_b` (the actual was resolved in the callee-wins β instead of the caller's), so
   the **bit never propagated**, the alternating bit never matched, and nothing was ever
   delivered (`Pmax(◇ delivered) = 0`). Fixed → P1 = 1, P3 = 1.
3. **Silent-drop deadlock** (modelling error in the *adaptation*, not the translator).
   An earlier version modelled channel loss as a plain silent drop (`i.s3(d,b) + i`).
   Under `--nofixdl`, `mcsta` exposed a reachable deadlock: after a drop the sender waits
   forever for an ack with no retransmission trigger. The translator had reproduced it
   **faithfully**. Corrected by restoring the always-deliver-something shape via the
   corrupted-frame signal (adaptation #4), which is deadlock-free.

A prerequisite change, the per-automaton syncs-matrix alphabet (`daf5e227d2`), was also
needed: before it, ABP's syncs matrix blew up and the tool hung before producing any JANI.

## Reproducing

```bash
# from repo root, with mcrl22jani built into build/stage/bin
build/stage/bin/mcrl22jani < tools/developer/mcrl22jani/case-studies/abp_closed.mcrl2 > abp.jani
# inject the `delivered` observer + P1/P2/P3 and run mcsta (delivered := true on R's s4
# edge; property expressions are given in the table above), then:
modest check          abp_with_properties.jani     # P1, P2, P3
modest check --nofixdl abp_with_properties.jani     # P4: reports a deadlock if any exists
```

## Limitations

- **Qualitative only.** ABP carries no probabilities, so results are `0`/`1`. Numeric
  reference-value validation (against the PRISM / QVBS benchmark suite) is planned for
  the *probabilistic* case study, `self_stabilisation`.
- **Properties are injected.** `mcrl22jani` emits no JANI `properties` yet, and delivery
  is observed via an added `delivered` flag rather than a native action-based property.
- **Deadlock-freedom depends on `--nofixdl`.** With `mcsta`'s default deadlock-repair
  (self-loops on sink states) a deadlock would be silently masked; P4 is only meaningful
  because the check is run with `--nofixdl`.
