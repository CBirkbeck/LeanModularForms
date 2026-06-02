/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HW33Clean

/-!
# Cauchy-theorem corollaries of HW Theorem 3.3

This file derives standard Cauchy-theorem statements from the
fully-general `hw_3_3_clean_full_mero` by specializing `S := ∅`.

When the singular set is empty, all of HW 3.3's hypotheses about
meromorphic structure, condition (A'), condition (B), and the
basepoint-off-singular-set side condition are vacuous, leaving exactly
the classical Cauchy theorem on a null-homologous piecewise-`C¹` closed
immersion in an open set.

## Main result

* `cauchy_integral_zero_pwc1` — Cauchy's theorem on a piecewise-`C¹`
  closed immersion that is null-homologous in an open set on which `f`
  is holomorphic. Proof: specialize `hw_3_3_clean_full_mero` with
  `S = ∅`.
-/

noncomputable section

namespace LeanModularForms

open Set Complex Filter Topology Finset
open scoped Real

variable {x : ℂ}

/-- **Cauchy's theorem on a piecewise-`C¹` closed immersion**, derived as the
`S = ∅` case of `hw_3_3_clean_full_mero` (HW Theorem 3.3, paper-faithful
clean form).

If `γ : ClosedPwC1Immersion x` is null-homologous in an open set `U ⊆ ℂ`
and `f : ℂ → ℂ` is holomorphic on `U`, then the contour integral of `f`
along `γ` is zero.

The proof specializes the general residue theorem with no singularities:
all of the conditions `hMero`, `hCondA`, `hCondB`, and `hx_notin_S` become
vacuous when `S = ∅`, and the empty residue sum vanishes. The CPV
predicate degenerates to the ordinary contour integral via
`hasCauchyPVOn_of_avoids`, and uniqueness of the limit gives the result. -/
theorem cauchy_integral_zero_pwc1
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (_hx : x ∈ U) :
    γ.toPwC1Immersion.toPiecewiseC1Path.contourIntegral f = 0 := by
  classical
  set S : Finset ℂ := ∅
  -- All HW33 hypotheses with `S = ∅` are trivial or vacuous.
  have hS_in_U : (↑S : Set ℂ) ⊆ U := by
    simp [S]
  have hf_diff : DifferentiableOn ℂ f (U \ ↑S) := by
    simpa [S, Finset.coe_empty] using hf
  have hMero : ∀ s ∈ S, MeromorphicAt f s := by intro s hs; cases hs
  have hCondB : SatisfiesConditionB γ.toPwC1Immersion f S :=
    { angle_rational := fun s hs _ _ _ _ => absurd hs (Finset.notMem_empty _)
      laurent_compatible := fun s hs _ _ _ _ => absurd hs (Finset.notMem_empty _) }
  have hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s =>
        (HungerbuhlerWasem.PolarPartDecomposition.ofMeromorphicWithCondB
          hU_open hS_in_U hf_diff
          (γ := γ.toPwC1Immersion) hMero hCondB).order s) := by
    intro s hs _ _ _ _; exact absurd hs (Finset.notMem_empty _)
  have hx_notin_S : x ∉ (↑S : Set ℂ) := by
    simp [S]
  -- Apply HW 3.3, then read off the empty residue sum.
  have h_cpv := hw_3_3_clean_full_mero hU_open hU_ne hS_in_U hf_diff
    γ h_null hMero hCondB hCondA hx_notin_S
  have h_sum : (∑ s ∈ S, 2 * ↑Real.pi * I *
      generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
        residue f s) = 0 := by simp [S]
  rw [h_sum] at h_cpv
  -- γ trivially avoids ∅, so the CPV equals the ordinary contour integral.
  have h_avoids : HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (γ.toPwC1Immersion.toPiecewiseC1Path.contourIntegral f) :=
    hasCauchyPVOn_of_avoids
      ⟨1, one_pos, by intro s hs; cases hs⟩
  -- Limits in HasCauchyPVOn are unique.
  exact tendsto_nhds_unique h_avoids h_cpv

end LeanModularForms

end
