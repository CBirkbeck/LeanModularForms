# Development Plan: HW Theorem 3.3 Tight Statement

## Goal

Produce a paper-style tight theorem `hw_3_3`:

```lean
theorem hw_3_3
    {U : Set ℂ} (hU : IsOpen U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S)
    (h_no_endpt_cross : ∀ s ∈ S,
      γ.toPiecewiseC1Path 0 ≠ s ∧ γ.toPiecewiseC1Path 1 ≠ s)
    (h_unique_cross : ∀ s ∈ S, ∀ t₁ ∈ Icc (0 : ℝ) 1, ∀ t₂ ∈ Icc (0 : ℝ) 1,
      γ.toPiecewiseC1Path t₁ = s → γ.toPiecewiseC1Path t₂ = s → t₁ = t₂) :
    HasCauchyPVOn S f γ.toPiecewiseC1Path
      (2 * π * I * ∑ s ∈ S, n_γ(s) · res_s(f))
```

Compared to the current `generalizedResidueTheorem_higherOrder_under_B_closed`, we eliminate:
- `h_polar`, `h_holo`, `h_decomp` (Laurent decomposition functions)
- `h_polar_cancel`, `h_holo_cancel` (CPV-vanishing of each part)
- `hI_polar`, `hI_holo`, `hI_sing` (integrability of each part)
- `hPV_sing` (singular-part PV formula)

These are derived automatically from `hMero`, `hCondB`, `hf_diff`, `h_null`.

## References

- Hungerbühler-Wasem (arXiv:1808.00997v2), Theorem 3.3
- `SatisfiesConditionB` in `FlatnessConditions.lean` — already carries Laurent
  decomposition via `laurent_compatible`
- Existing `generalizedResidueTheorem_higherOrder_under_B_closed` — input form

## Mathlib Inventory

| Concept | Status | Action |
|---------|--------|--------|
| `MeromorphicAt` | mathlib | USE |
| `meromorphicTrailingCoeffAt` | mathlib | USE for residue |
| `principalPartSum` (simple) | this project | USE |
| Laurent polar part (general) | NOT in mathlib | EXTRACT from `SatisfiesConditionB.laurent_compatible` |
| Holomorphic remainder | NOT directly | DEFINE as `f - polarPart` |

## File Structure

- `HW33LaurentPolarPart.lean` (NEW) — extract Laurent decomposition from `SatisfiesConditionB`
- `HW33Tight.lean` (NEW) — the tight theorem `hw_3_3`

## Dependency Graph

```
SatisfiesConditionB.laurent_compatible
    ↓ (extract)
laurentPolarPartAt s     -- per-pole Laurent polar part
    ↓ (sum over S)
laurentPolarPartTotal f S    -- global polar function
    ↓ (subtract from f)
laurentHolomorphicRemainder f S   -- analytic on U \ accumulation
    ↓ (CPV vanishing via existing closure + Cauchy)
hCancel discharge
    ↓
hw_3_3 (final tight theorem)
```

## Generality Decisions

- Take `γ : PwC1Immersion` (existing type)
- Take `S : Finset ℂ` (matches existing closure)
- Keep `h_no_endpt_cross` and `h_unique_cross` — these are technical conditions
  about γ's parametrization, not derivable from f's data

## Strategy Notes

The key insight: `SatisfiesConditionB` already contains Laurent data via
`laurent_compatible : ∀ s ∈ S, ..., ∃ N a g, ...`. We extract this via
`Classical.choose` (which only requires `Classical.choice` axiom — already
in our axiom set). The extracted data feeds directly into our (B)-closure
machinery.
