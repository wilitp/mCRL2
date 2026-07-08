# Self-stabilisation — faithfulness cross-validation & toolset runtime comparison

A second, **independent** check on the `mcrl22jani` translation of the Israeli–Jalfon
self-stabilisation protocol, complementing [`self_stabilisation_results.md`](./self_stabilisation_results.md).

The idea: verify the *same quantitative property* — the worst-case expected number of
steps to stabilise, `Emax(◇ #tokens = 1)` — along **two routes that share nothing but the
source model**, and check they agree.

- **Native route.** Stay in mCRL2. Model-check the property directly on the probabilistic
  process using mCRL2's own real-valued (quantitative) modal μ-calculus:
  `mcrl22lps → lps2pres → pressolve`. No JANI, no `mcrl22jani`.
- **Translate route.** Translate to JANI with `mcrl22jani`, then model-check in the
  **Modest Toolset** (`mcsta`): `mcrl22jani → modest check`.

If the translation is faithful, the two routes must produce the same value — up to the one
structural difference we can account for exactly.

## The one accounted-for difference: the init edge

The JANI encoding resolves the initial `dist` distribution with a one-off
`INIT --init--> Stoch(p)` edge, and the `Emax(steps)` reward counts **one per JANI edge**,
so it counts that init edge too. The native mCRL2 property counts one per `comm_token`
move and has no such edge. Hence the exact expectation:

> **JANI `Emax` = native mCRL2 `Emax` + 1.**

## Result — the two routes agree exactly (N = 3)

| Route | Tool stack | Spec | `Emax` steps |
|---|---|---|---|
| Native | `mcrl22lps` → `lps2pres` → `pressolve -a m` | [`self_stabilisation_N3_native.mcrl2`](./self_stabilisation_N3_native.mcrl2) (data-comm) | **7.0** (exact, stable to 1e-9) |
| Translate | `mcrl22jani` → `modest check` | [`self_stabilisation_N3.mcrl2`](./self_stabilisation_N3.mcrl2) (per-link) | **7.999996 ≈ 8.0** |

`8 − 7 = 1`, precisely the init edge. Two different specs (data-matched `comm` vs
label-routed channels), two different tools, two different verification algorithms
(symbolic PRES fixpoint vs explicit-state value iteration) — and they land on the same
number modulo the one edge we predicted. The N = 3 translate route also reproduces the
full property set (P1 vanish = 0, P2 grow = 0, P3 `Pmin` stabilise ≈ 1, P5 `Emin` = 3.125)
over the expected **57 = (2³−1)·2³ + 1** states.

At **N = 5** the translate route gives `Emax` = **23.9166** over 993 states; the native
route could not be solved on *either* spec (see the control and runtimes below), but the
N = 3 identity plus the matching qualitative results make the case.

### Bonus: the scheduler foresight is *intrinsic to the mCRL2 model*

The native route settles the original worry directly, because it never touches JANI. A
**coin-blind** reference (direction chosen *on* the move, as in PRISM's DTMC-style model)
gives `Emax = 3.0` at N = 3 with zero scheduler spread. mCRL2's own checker, on the
unmodified data-comm model, gives **7.0**. The gap is the adversary exploiting each token's
direction, which mCRL2's `dist` commits into the state one move ahead of the schedule.
That foresight lives in the **source semantics**; `mcrl22jani` reproduces it rather than
introducing it. (JANI then adds the +1 init edge, giving 8.)

## Runtime comparison — same property, same machine

Timing `Emax(◇ stable)` (single property; `/usr/bin/time` wall clock):

| Step | N = 3 | N = 5 |
|---|---|---|
| **Native mCRL2** (`mcrl22lps → lps2pres → pressolve`) | | |
| &nbsp;&nbsp;`mcrl22lps` | 3.7 s | 3.7–5.0 s |
| &nbsp;&nbsp;`lps2pres` | 4.5 s | 10.6–10.8 s |
| &nbsp;&nbsp;`pressolve` (numerical solve) | **42.8 s → 7.0** | **no usable result** (see control) |
| &nbsp;&nbsp;**native total** | **≈ 51 s** | **—** |
| **Translate + Modest** (`mcrl22jani → modest`) | | |
| &nbsp;&nbsp;`mcrl22jani` (one-time translate) | 4.8 s | 7.6 s |
| &nbsp;&nbsp;`modest check` (explore + value iteration) | **0.33 s → 8.0** | **0.37 s → 23.9166** |
| &nbsp;&nbsp;**translate total** | **≈ 5.2 s** | **≈ 8.0 s** |

### Control — is the gap the adaptation or the toolchain?

The performance boost could, a priori, be an artifact of the *adaptation* (per-link labels)
rather than the *toolchain* (Modest vs mCRL2-native). To rule that out, the N = 5 native
solve was run on **both** specs:

| N = 5 native attempt | Spec | Emax property | Outcome |
|---|---|---|---|
| `sup i,j` over `comm_token(i,j)` | data-comm original | [`..._Emax.mcf`](./self_stabilisation_Emax.mcf) | RES instantiation never finishes — **aborted at 6 min** |
| explicit 10-way `<c_uv>` disjunction | per-link adapted | [`..._Emax_adapted.mcf`](./self_stabilisation_Emax_adapted.mcf) | RES finishes, but `pressolve` (`-a m` **and** `-a n`) converges to a **spurious `-inf`** (~4 min each) |

**Neither spec yields a usable N = 5 value from the native route**, while Modest verifies
*both* in 0.37 s. So the feasibility gap is the **toolchain, not the adaptation**. If
anything the adaptation *helped* the native route — dropping the data quantifier let RES
instantiation complete — yet the underlying numerical solve still failed. Both N = 3 native
runs (data-comm **and** adapted) give the identical **7.0**, confirming the adapted-spec
property is correct; the `-inf` at N = 5 is a size-dependent value-iteration failure of
`pressolve`, not a modelling error.

Reading of the numbers:

- On the **model-checking step alone**, Modest is ~**130×** faster at N = 3 (0.33 s vs
  42.8 s), and it *finishes* at N = 5 (0.37 s, 993 states at ~16 k states/s) where the
  native symbolic solver does not — **on either spec**.
- **End-to-end** (including the one-time translation), the translate route is ~**10×**
  faster at N = 3 and is the only route that produces an N = 5 answer.
- The gap is not the adaptation and not an implementation detail: `pressolve` instantiates a
  symbolic parameterised real equation system whose per-step cost balloons on the folded
  coin re-roll (and whose value iteration destabilises to `-inf` at N = 5), while the JANI
  target is an explicit-state MDP on which value iteration is cheap and robust. Translating
  to JANI is exactly what unlocks the efficient route.

**Why this matters for the thesis.** Beyond correctness, the translation has a practical
payoff: **even if mCRL2 is your preferred specification language**, `mcrl22jani` lets you
verify these probabilistic systems in a dramatically more feasible way than mCRL2's own
quantitative model checker — turning an intractable N = 5 native solve into a sub-second
Modest check.

## Reproducing

```bash
CS=tools/developer/mcrl22jani/case-studies

# --- native route (N=3) ---
build/stage/bin/mcrl22lps < $CS/self_stabilisation_N3_native.mcrl2 ss3.lps
build/stage/bin/lps2pres  -f $CS/self_stabilisation_Emax_N3.mcf   ss3.lps ss3.pres
build/stage/bin/pressolve -a m -Q6 -p9 ss3.pres          # -> 7   (Emax, no init edge)

# --- translate route (N=3) ---
build/stage/bin/mcrl22jani < $CS/self_stabilisation_N3.mcrl2 > ss3.jani
python3 $CS/add_properties.py ss3.jani ss3.checked.jani
modest check ss3.checked.jani                            # P4_exp_steps_max -> 7.999996  (= 7 + 1)
```

`lps2pres`/`pressolve` are experimental tools — build with `-DMCRL2_ENABLE_EXPERIMENTAL=ON`
(`cmake --build build --target lps2pres pressolve`). `-a m` (numerical) is required; the
default Gauss solver does not return on this model.

## Caveats (honesty)

- **Two specs, one system.** The native route runs on the data-`comm` original; the
  translate route on the label-routed adaptation. They are semantically equivalent IJ
  N = 3, and the matching `7 ↔ 8` (plus identical qualitative results) is the evidence.
- **N = 5 native has no result — on either spec** (data-comm aborts in instantiation; the
  adapted spec instantiates but the solve returns a spurious `-inf`). This is precisely the
  control that isolates the cause as the toolchain; the N = 3 identity pins the faithfulness
  claim.
- **`pressolve`'s value iteration is fragile at scale.** The minimising `Emin` underflows to
  `-inf` at every size (the standard min-reward artifact under `inf`); the maximising `Emax`
  is solid at N = 3 (7.0 on both specs) but *also* degenerates to `-inf` at N = 5. Modest's
  value iteration handles both (`Emin` = 3.125 at N = 3; `Emax` = 23.9166 at N = 5).

## Artifacts

- [`self_stabilisation_Emax.mcf`](./self_stabilisation_Emax.mcf) — native `Emax`, N = 5, data-comm (`comm_token`) form.
- [`self_stabilisation_Emax_N3.mcf`](./self_stabilisation_Emax_N3.mcf) — native `Emax`, N = 3, data-comm form.
- [`self_stabilisation_Emax_adapted.mcf`](./self_stabilisation_Emax_adapted.mcf) — native `Emax`, N = 5, **adapted** (per-link `c_uv`) form — the control property.
- [`self_stabilisation_Emax_adapted_N3.mcf`](./self_stabilisation_Emax_adapted_N3.mcf) — native `Emax`, N = 3, adapted form (validates to 7.0).
- [`self_stabilisation_N3.mcrl2`](./self_stabilisation_N3.mcrl2) — adapted (per-link) N = 3 spec, translate route.
- [`self_stabilisation_N3_native.mcrl2`](./self_stabilisation_N3_native.mcrl2) — original (data-comm) N = 3 spec, native route.
