# Ticket A2 — Remove `sorryAx` from the Ticket A theorem chain — **DONE** ✓

## Scope

Edit only:
- `PiecewiseHomotopy.lean`
- `Infrastructure/PiecewiseHomotopyHelpers.lean`
- `VALENCE_AI_PROGRESS.md`

Do not edit Ticket C files or PV files (separate worker owns those).

## Objective

`generalizedWindingNumber_fdBoundary_eq_neg_one` is proof-complete but still depends on `sorryAx`.
Eliminate the remaining executable `sorry`s in the piecewise homotopy infrastructure and remove
`sorryAx` from:
- `windingNumber_eq_of_piecewise_homotopic`
- `generalizedWindingNumber_fdBoundary_eq_neg_one`

## Root-cause policy

Do not try to prove no-bound statements from open-piece continuity alone.
Refactor those statements to require explicit derivative-bound existence hypotheses and route to
existing `_with_bound` lemmas.

## Required implementation order

1. Add a micro-helper in `PiecewiseHomotopy.lean`:
   - from homotopy `hM_bound` + fixed `s ∈ Icc 0 1`, produce a slice derivative bound witness.

2. Refactor `windingNumber_integer_of_piecewise_closed_avoiding`:
   - add `hγ_deriv_bound_ex : ∃ M, ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M`
   - replace body with wrapper call to
     `windingNumber_integer_of_piecewise_closed_avoiding_with_bound`.

3. Refactor `windingNumber_continuousOn_param_piecewise` in
   `Infrastructure/PiecewiseHomotopyHelpers.lean`:
   - add
     `hH_deriv_bound_ex : ∃ M, ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, ‖deriv (fun t' => H (t', s)) t‖ ≤ M`
   - replace body with wrapper call to
     `windingNumber_continuousOn_param_piecewise_with_bound`.

4. Refactor `windingNumber_continuous_in_param_piecewise` in `PiecewiseHomotopy.lean`:
   - add matching bound-existence hypothesis
   - route to refactored helper theorem.

5. Update `windingNumber_eq_of_piecewise_homotopic` call sites:
   - pass derivative-bound existence witness from homotopy field `hM_bound`.

## Non-negotiable worker rules

- Micro-lemmas only: no proof block longer than ~8 lines without `have`.
- Do not delete failed attempts; leave exact goal + error in a short comment.
- If blocked >10 minutes, stop and report exact goal + Lean error.
- Do not alter theorem orientation/sign (`..._eq_neg_one` stays unchanged).

## Required verification commands

1. `rg -n "\\bsorry\\b" PiecewiseHomotopy.lean Infrastructure/PiecewiseHomotopyHelpers.lean`
2. `lake build LeanModularForms.Modularforms.valence.ComplexAnalysis.PiecewiseHomotopy`
3. `lake build LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Rect_Homotopy`
4. `#print axioms windingNumber_eq_of_piecewise_homotopic`
5. `#print axioms generalizedWindingNumber_fdBoundary_eq_neg_one`

## Done criteria

- no executable `sorry` remains in the two target infrastructure files,
- no `sorryAx` in the two axiom checks above,
- `VALENCE_AI_PROGRESS.md` updated with exact signatures changed, sorry count delta, and build results.

## Completion Record (2026-02-10)

**All done criteria met:**
- 0 sorries in both target files (rg confirms no matches)
- No `sorryAx` — both `#print axioms` show only `[propext, Classical.choice, Quot.sound]`
- `VALENCE_AI_PROGRESS.md` updated with full details and raw command outputs
