# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository context

This is a fork of the [mCRL2 toolset](https://mcrl2.org) used as a thesis project. The
active work is the **`mcrl22jani`** developer tool, which translates an mCRL2 process
specification into the [JANI](https://jani-spec.org/) model-interchange format. Almost all
day-to-day work happens in `tools/developer/mcrl22jani/`; the rest of the repo is upstream
mCRL2 and is rarely touched (a few generated/parser files aside).

Branch of interest: `mcrl22jani` (PRs usually target `master`).

## Formal specification (the thesis)

The translation is specified by the thesis, written in LaTeX (Spanish) and symlinked into the
tool dir at `tools/developer/mcrl22jani/latex/` (the symlink points outside the repo). **These
`.tex` chapters are the authoritative spec — read them before implementing or changing
translation logic, and re-read rather than trusting any restatement here, because the author
edits them and the formulas can change.** Core chapters:

- `mcrl2.tex` — the supported mCRL2 subset and its informal semantics. Grammar:
  `p ::= ω[(t…)] | p+p | p·p | δ | c→p◇p | Σ_{d:D} p | dist_{d:D}[f(d)] p | p‖p | Γ_C(p) |
  ∇_V(p) | ∂_B(p) | ρ_R(p) | τ_I(p) | X[(t…)]`.
- `jani.tex` — the target domain and JANI schema used: a **symbolic MDP**
  `(Loc, l₀, Act, Var, v₀, →)` with `→ ⊆ Loc × Act × Bxp × Wxp`, targets
  `𝒲 ∈ Wxp = [Asgn] × Loc → Exp` (symbolic distributions over (indexed-assignment-list,
  location) pairs), `𝒟(as,l)` the Dirac mass. Also: JANI `syncs`/`Composition`, and
  communication via **transient global variables** + assignment **indices** (lower index runs
  first; equal indices are simultaneous).
- `traduccion.tex` — the actual translation. The load-bearing parts:
  - **Read/write action discipline.** Since JANI has no `sum`, a `sum d:D` is read as
    *receiving a value*. Actions partition into disjoint `Act_read` (carry the first occurrence
    of a sum-bound var, passed *bare* — no `n+1`, no constants) and `Act_write`. `γ: Act_write →
    𝒫(Act_read)` is the communication map. A write pushes args into each communicating read's
    comm-vars at index 0; the read pulls at index 1 (strictly after writers).
  - **`Stoch(p)`** — the initial state *distribution* (because `dist` can front-load
    probability); resolved by an `INIT --init--> Stoch(p)` edge.
  - **SOS rules** `p --c,ω--> 𝒲` for each operator, plus the assignment-list operators
    `restrict`, `coin`, `++*` (`iconcat`), `++_*` (`iiconcat`).
  - **Syncs matrix** `[a⃗ | α]` (sync vector → resulting multi-action): basic process =
    identity rows (any action independently); `‖` = independent + all-pairs sync rows;
    `∇`/`∂`/`ρ`/`Γ` as row filters/renames; a final all-`init` row synchronises the initial
    `Stoch` resolution across automata.

`introduccion.tex` is background/motivation only.

**Location identity = the thesis triple.** `process_location` is `(expr, β, env)` matching
`Loc = ProcExp × (mCRL2Var → JANIVar) × [Asgn]`: process expression, β symbol map, and `env`
(the pending substitution environment, `std::map<data::variable, data::data_expression>`).
`makeLoc` restricts β/env to the **free variables** of `expr` (keeping β bindings any env-RHS
expression still needs) so identity is canonical, and `locationName` renders `expr` through β/env
(so `b(n)` under `n↦P_n` vs `n↦Q_n` becomes `b(P_n)` vs `b(Q_n)` instead of colliding). Every
**stored/reachable** location has empty `env`; `env` is non-empty only on the transient
`(body, β, env)` locations used to compute a process instance's transitions (below) and, later,
once `dist` lands. The substitution lives in the location *for identity* **and** on edges *for
behavior* — two jobs, not a duplication.

**Process-instance transitions are computed recursively (Recursión/Fijación).** `successors`
threads two head-chain values that reset at every action boundary: `env` (mCRL2 substitution,
composed per-equation, used to resolve guards via `replace_variables` before conversion) and
`pending` (a `json::array` of edge assignments, accumulated, emitted on the next action edge).
A process instance `P(t)` is handled by `enterInstance`, which builds the body's first-class —
but **never stored** — location `(body, mergedβ, env')` and recurses: `mergedβ = β ∪ βP` with
the **callee winning** on same-named formals (so `P`/`Q` both using `n` resolve to `P_n`/`Q_n`);
`env'` composes the substitution into the actuals (for guards, which must not read a var set on
the same edge); `pending` gains this instance's `βP(dᵢ) := convert(actualᵢ)` with the actual left
**symbolic**, merged via `iiconcat` (the thesis `++_*`) so an outer instance's assignments take
lower indices and run first (within one instance all dᵢ share an index → simultaneous, e.g. a
`P(y,x)` swap). Indices are normalized non-negative at the action edge. Tails reached via
`seqTarget` are env-/pending-free and stay symbolic, so recursion through process identifiers
terminates (the `unfolding` set rejects unguarded recursion). This is faithful to the thesis
Fijación/Recursión rules (`c' = as(c)`, `W' = as ++_* bs`) and fixes the cross-scope-guard
unsoundness the earlier eager inlining (`substituteHeadGuards`/`makeParamAssignments`) had.

## Build & run

The configured out-of-source build lives in `build/` (Unix Makefiles, `Debug`,
`MCRL2_ENABLE_DEVELOPER=ON`). Binaries are staged into `build/stage/bin/`.

```bash
# Build only the tool (fast; this is what the VS Code "build mcrl22jani" task runs)
cmake --build build --target mcrl22jani

# Reconfigure from scratch if needed (Qt6 + Boost >= 1.75 required for boost::json)
cmake -S . -B build -DCMAKE_BUILD_TYPE=Debug

# Run: reads an mCRL2 spec from stdin (or a file arg), writes JANI JSON to stdout
build/stage/bin/mcrl22jani < some_spec.mcrl2
build/stage/bin/mcrl22jani some_spec.mcrl2 > out.jani
```

`mcrl22jani` requires `MCRL2_ENABLE_BOOST_JSON_SUPPORT=ON` (its `CMakeLists.txt` is guarded
by it) and is only built when `MCRL2_ENABLE_DEVELOPER=ON`.

Note: the repo root also contains an in-source build (`Makefile`, `stage/`, `CMakeCache.txt`)
left over from an earlier configuration. Prefer `build/` — it is what `.vscode/tasks.json`
and `compile_commands.json` point at.

### Tests

The upstream toolset uses CTest (`ctest` from a build dir; `MCRL2_ENABLE_TESTS` /
`MCRL2_ENABLE_TOOL_TESTS`). `mcrl22jani` currently has no registered tests of its own —
verify changes by running the tool on a spec and inspecting the JANI output.

## mcrl22jani architecture

Everything lives in the single file `tools/developer/mcrl22jani/mcrl22jani.cpp` (~1700 lines).
The tool deliberately does **not** linearise the spec (the `linearise(...)` call is left
commented out); it translates the process algebra directly. Key pieces, in dependency order:

- **`mcrl22jani_tool`** (`rewriter_tool<input_output_tool>`) — CLI entry point. Parses a
  `process_specification` via `mcrl2::process::parse_process_specification`, then hands it to
  `jani_translator`. No tool-specific options yet.

- **`jani_translator`** — top-level orchestrator (`translate_process_specification`). The
  init expression is treated as a **parallel composition of pCRL processes**: each operand
  becomes one JANI automaton, and the parallel/communication operators
  (`merge`/`allow`/`block`/`hide`/`rename`/`comm`) are folded into a `syncs_matrix` rather
  than into the automata themselves. Produces a JANI model of `"type": "mdp"`.

- **`pcrl_to_automaton_translator`** — translates one sequential (pCRL) process into a JANI
  automaton. This is a **graph traversal, not an AST traversal**: a location (`abstract_location
  = variant<process_location, termination_t>`) is the triple `(expr, β, env)` (see "Location
  identity" below). The translator works-list-explores outgoing transitions, deduplicating
  already-discovered locations (recursion via process identifiers makes this necessary). See
  `plan.md` in the same dir for the design narrative.

- **`syncs_matrix`** — models multi-party action synchronisation. mCRL2 channels are mapped to
  JANI by splitting each communicating action into **writing** vs **reading** actions; the
  matrix's rows are sync vectors (left = ordered actions per automaton, right = resulting
  multi-action). `checkSyncs` enforces exactly one writer per sync; `addMissingAssignments`
  back-fills reads. Built recursively (`buildSyncsMatrixRec`) by interpreting the parallel
  operators, with operators `||`, `.allow()`, `.block()`, `.hide()`, `.rename()`.

- **Data/sort conversion** — `convert_sort_expression` and `convert_data_expression` map
  mCRL2 sorts/expressions to JANI. JANI only supports `bool`/`int`/`real` plus bounded
  variants for `nat`/`pos`; unsupported sorts throw `jani_translation_error`. Note JANI lacks
  `>` / `>=`, so those are flipped to `<` / `<=`.

Translation errors are raised as `jani_translation_error` (a `mcrl2::runtime_error`). Progress
and well-formedness messages go through `mCRL2log(mcrl2::log::info|verbose)`.

`jani-spec.js` is a vendored copy of the JANI specification, kept as a reference for the
target schema.

## Upstream mCRL2 libraries (for context)

The translator builds on mCRL2's C++ libraries under `libraries/` (depended on:
`mcrl2_lps`, `mcrl2_lts`). Relevant ones:

- `process/` — process algebra AST: `process_expression`, the `is_*` type predicates and
  `down_cast<>` accessors (`merge`, `allow`, `comm`, `seq`, `choice`, `if_then`, `sum`,
  `process_instance`, …) used throughout the translator.
- `data/` — sorts, data expressions, rewriters (`rewriter_tool`).
- `lps/` — linear process specs and linearisation (available but intentionally unused here).
- `atermpp/` — the underlying ATerm term library (`down_cast`, term traversal).
- `core/` — parser/grammar; `source/mcrl2_syntax.c` is generated.

Tools are grouped by maturity under `tools/{release,developer,experimental,deprecated}/`,
each gated by an `MCRL2_ENABLE_*` option. New developer tools follow the pattern in
`mcrl22jani/CMakeLists.txt`: `mcrl2_add_tool(<name> SOURCES ... DEPENDS mcrl2_<lib> ...)`.

## Conventions

- Code style is enforced by `.clang-format` and `.clang-tidy` (LLVM-derived, mCRL2 tweaks).
- Every source file carries the Boost license header (see existing files for the exact block).
