# Self-stabilisation case study — evaluation results

Evaluation of the `mcrl22jani` translation on the **Israeli–Jalfon self-stabilisation**
protocol (token ring of 5), the probabilistic case study. As with ABP the goal is
*translation validation*: translate to JANI, load into the **Modest Toolset** (`mcsta`),
and check the result reproduces the protocol's known behaviour. Unlike ABP this model is
genuinely probabilistic (`dist`), so it also validates the `dist` / Stoch translation.

## Model under test

- **Spec:** [`self_stabilisation.mcrl2`](./self_stabilisation.mcrl2), adapted from
  `examples/probabilistic/self_stabilisation/self_stabilisation.mcrl2` (taken from the
  **PRISM Benchmark Suite**; Israeli & Jalfon 1990).
- **The adaptation — and why it is required.** The upstream model uses a single
  data-carrying channel and relies on mCRL2 `comm` matching the *data* two actions carry
  to route each token to the correct ring neighbour:
  `send_token(id,next) | read_token(next,id) -> comm_token`. **JANI/Modest synchronise on
  action *labels* only — the data is not matched during composition** — so that routing
  cannot survive translation (any send would sync with any read; the ring becomes a
  complete graph). The fix encodes the topology in the labels: one channel per directed
  link, `s_uv | r_uv -> c_uv`, with nullary actions (the token is process state, not
  action data). Semantics are unchanged: a token-holder passes to a uniformly-random
  neighbour (`dist b:Bool[1/2]`), tokens merge on contact.
- **Composition:** `P0 ‖ P1 ‖ P2 ‖ P3 ‖ P4`, all starting with a token → 5 automata,
  10 link channels + the initial-distribution sync. **Type:** JANI `mdp` (the scheduler
  chooses which token-holder moves; the coin chooses direction).

## Toolchain

| Component | Version / ref |
|---|---|
| `mcrl22jani` | this repo, branch `mcrl22jani`, translator at commit `f921327d39` |
| Modest Toolset (`mcsta`) | `v3.1.301-gfcaf4299f` |

`mcrl22jani` emits no JANI `properties`, so they were injected. "Number of tokens" is
observed by **promoting each automaton's `Pi_token` to a global variable** (a safe,
observation-only transform — each token var is written only by its own automaton) and
summing them; "stable" is `(#tokens == 1)`.

## State space (a structural check in itself)

`mcsta` explores **993 states / 2561 transitions**, and `993 = 31 × 32 + 1`: the 31
non-empty token subsets of 5 processes × the 32 (=2⁵) coin assignments, plus the initial
state. Exactly the reachable configuration set expected — no 0-token configuration, no
spurious states. This alone is good evidence the label-based routing is faithful.

## Properties checked

| # | Meaning | Formal | Result | Expected |
|---|---|---|---|---|
| P1 | token count never vanishes | `Pmax(◇ #tokens = 0)` | **0** | 0 |
| P2 | token count never grows | `Pmax(◇ #tokens > 5)` | **0** | 0 |
| P3 | **self-stabilises** (reaches 1 token) | `Pmin(◇ #tokens = 1)` | **1** | 1 |
| P4 | worst-case expected time to stabilise | `Emax(◇ #tokens = 1)` | **≈ 23.92** steps | finite, Θ(N²) |
| P5 | best-case expected time to stabilise | `Emin(◇ #tokens = 1)` | **≈ 6.73** steps | finite |

**P3 is exact, not just numerical.** Value iteration reports `0.99999…` (its convergence
tolerance), but `mcsta`'s qualitative precomputation reports **"Min. prob. 1 states: 993"**
— i.e. from *every* one of the 993 states, a stable configuration is reached with
probability 1 under the *worst-case* adversary. That is a graph-based proof that
`Pmin(◇ stable) = 1` exactly.

P4/P5 count `mcsta` transitions from the initial state; because the encoding pre-resolves
each process's coin (the randomness of a move is folded into the previous transition),
one token *move* is one transition, plus the one-off initial-distribution transition.

## Reference values and their source

**Reference:** A. Israeli and M. Jalfon, *Token management schemes and random walks yield
self-stabilizing mutual exclusion*, PODC 1990 — via the **PRISM Benchmark Suite**
(`prismmodelchecker.org/casestudies/self-stabilisation.php`), the model's cited origin.

- **Convergence with probability 1** is the defining guarantee of the protocol (self-
  stabilisation: from *any* configuration the system reaches a single-token / mutual-
  exclusion state a.s., under any scheduler). Our result **P3 = `Pmin(◇ stable) = 1`**,
  proven qualitatively (993/993 min-prob-1 states), matches this reference exactly.
- **Expected stabilisation time** is finite and, for the Israeli–Jalfon ring, grows as
  Θ(N²); for N = 5 the computed worst-case ≈ 23.9 steps sits right at N² = 25, the
  expected order of magnitude.

> The P4/P5 numbers are **reconciled** in
> [`self_stabilisation_faithfulness.md`](./self_stabilisation_faithfulness.md): the same
> `Emax` property, model-checked with mCRL2's *own* quantitative μ-calculus on the
> untranslated model, gives exactly `JANI value − 1` (the −1 being the counted init edge),
> and the worst-case value's excess over PRISM's blind-scheduler figure is intrinsic
> scheduler foresight present already in the mCRL2 semantics — not a translation artifact.

## What the evaluation surfaced

- **The headline finding: `comm` data-matching does not translate.** mCRL2 routes
  communication by matching the data actions carry; JANI/Modest sync purely on labels.
  Any model that leans on data-matched `comm` for addressing (as this one does, and as
  many mCRL2 models do) must be re-encoded with per-channel labels before translation.
  This is a genuine expressiveness boundary of the target, not a tool bug — worth stating
  in the thesis.
- The translation itself was faithful once adapted: correct link routing (verified per
  sync vector), exact token conservation, and the expected `31 × 32 + 1` state space.

## Reproducing

```bash
build/stage/bin/mcrl22jani < tools/developer/mcrl22jani/case-studies/self_stabilisation.mcrl2 > ss.jani
# promote each Pi_token to a global var (initial value true), add the properties over
# (#tokens = sum of Pi_token), then:
modest check          ss_with_properties.jani   # P1, P2, P3, P4, P5
modest check --nofixdl ss_with_properties.jani   # confirm no reachable deadlock
```

## Limitations

- **Properties are injected**, and token counting relies on promoting the per-automaton
  `Pi_token` to globals (Modest cannot reference automaton-local variables in properties).
- **Numeric expected-time** is reconciled against an independent mCRL2-native check in
  [`self_stabilisation_faithfulness.md`](./self_stabilisation_faithfulness.md) (which also
  compares toolset runtimes); the exact self-stabilisation guarantee (`Pmin = 1`) remains
  the direct reference-value match.
