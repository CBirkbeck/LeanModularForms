/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDWindingDataFullSeg1Seg4
import LeanModularForms.ForMathlib.ResidueSideBridge

/-!
# Fully-ForMathlib Valence Formula (via bridged residue/modular sides)

This file combines:
- `valence_formula_unconditional_mkD` (the top-level valence formula with
  `mkD` baked in, requiring residue/modular side Tendsto hypotheses)
- `cpv_residue_side_HasCauchyPVOn` and `cpv_modular_side_HasCauchyPVOn`
  (the residue/modular side results bridged from the old chain)

The end result is a ForMathlib-native, axiom-clean final valence formula
theorem that requires only `hf : f ≠ 0` as input.

## Main result

* `valence_formula_textbook_unconditional_FM` — the fully unconditional
  valence formula in the ForMathlib chain
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-- The integrand we use to combine residue and modular sides:
  `F_int H ε = ∫ t in 0..1, cpvIntegrandOn (sArcOfS S ∪ sVertOfS S) (logDeriv f) γ.extend ε t`
where `γ = (fdWindingDataFull_unconditional hH).boundary`. -/
private noncomputable def F_int_FM (S : Finset UpperHalfPlane) (H : ℝ) (ε : ℝ) : ℂ :=
  if hH : 1 < H then
    ∫ t in (0 : ℝ)..1,
      cpvIntegrandOn (sArcOfS S ∪ sVertOfS S)
        (logDeriv (modularFormCompOfComplex f))
        (fdWindingDataFull_unconditional hH).boundary.toPath.extend ε t
  else 0

include hf in
/-- **Final unconditional valence formula**, combining
`valence_formula_unconditional_mkD` with `cpv_residue_side_HasCauchyPVOn` and
`cpv_modular_side_HasCauchyPVOn` from `ResidueSideBridge`. -/
theorem valence_formula_textbook_unconditional_FM
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (H_S : ℝ) (hH_S : ∀ s ∈ S, (s : ℂ).im < H_S) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
        ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ sLeftVertFM S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 := by
  -- Get the residue and modular side bridges
  obtain ⟨H₀_res, hH₀_res, h_res_bridge⟩ :=
    cpv_residue_side_HasCauchyPVOn f hf S hS hS_complete
  obtain ⟨H₀_mod, hH₀_mod, h_mod_bridge⟩ :=
    cpv_modular_side_HasCauchyPVOn f hf S hS hS_complete
  -- Pick max(H₀_res, H₀_mod, H_S, 1) + 1 to get H > 1 and above all bounds
  set H_res := max (max (max H₀_res H₀_mod) H_S) 1 + 1 with hH_res_def
  have hH_res_gt : (1 : ℝ) < H_res := by
    rw [hH_res_def]
    have h1 : (1 : ℝ) ≤ max (max (max H₀_res H₀_mod) H_S) 1 := le_max_right _ _
    linarith
  have hH₀_res_le : H₀_res ≤ H_res := by
    rw [hH_res_def]
    have h1 : H₀_res ≤ max H₀_res H₀_mod := le_max_left _ _
    have h2 : max H₀_res H₀_mod ≤ max (max H₀_res H₀_mod) H_S := le_max_left _ _
    have h3 : max (max H₀_res H₀_mod) H_S ≤ max (max (max H₀_res H₀_mod) H_S) 1 :=
      le_max_left _ _
    linarith
  have hH₀_mod_le : H₀_mod ≤ H_res := by
    rw [hH_res_def]
    have h1 : H₀_mod ≤ max H₀_res H₀_mod := le_max_right _ _
    have h2 : max H₀_res H₀_mod ≤ max (max H₀_res H₀_mod) H_S := le_max_left _ _
    have h3 : max (max H₀_res H₀_mod) H_S ≤ max (max (max H₀_res H₀_mod) H_S) 1 :=
      le_max_left _ _
    linarith
  have hH_S_le : H_S ≤ H_res := by
    rw [hH_res_def]
    have h1 : H_S ≤ max (max H₀_res H₀_mod) H_S := le_max_right _ _
    have h2 : max (max H₀_res H₀_mod) H_S ≤ max (max (max H₀_res H₀_mod) H_S) 1 :=
      le_max_left _ _
    linarith
  -- Apply valence_formula_unconditional_mkD with explicit residue/modular sides
  refine valence_formula_unconditional_mkD f S hS hS_complete H_S hH_S (F_int_FM f S)
    H_res hH_res_gt ?_ H_res hH_res_gt ?_
  · -- Residue side: F_int → 2πi · Σ gWN · ord
    intro H hH_ge hH
    have hH_ge_res : H₀_res ≤ H := le_trans hH₀_res_le hH_ge
    set γ := (fdWindingDataFull_unconditional hH).boundary with hγ_def
    have hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t :=
      (fdWindingDataFull_unconditional hH).boundary_eq
    have h_pv := h_res_bridge hH_ge_res γ hγ
    -- Use the reverse bridge to convert old chain gWN' to new chain gWN
    -- For each s, gWN' γ s = gWN γ s (via generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber)
    -- This requires HasGeneralizedWindingNumber γ s w, which we get from FDWindingDataFull
    have hH_above : ∀ s ∈ S, (s : ℂ).im < H := fun s hs =>
      lt_of_lt_of_le (hH_S s hs) (le_trans hH_S_le hH_ge)
    -- For each s ∈ S ⊆ 𝒟, derive gWN' = gWN via the per-point bridge
    have h_gwn_eq : ∀ s ∈ S,
        generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) =
        generalizedWindingNumber γ (↑s : ℂ) := by
      intro s hs_S
      have hs_fd := hS s hs_S
      have hs_im_lt : (s : ℂ).im < H := hH_above s hs_S
      -- Get HasGeneralizedWindingNumber γ s w via case split
      -- Cases: s = i, s = ρ, s = ρ+1, strict interior, or boundary
      by_cases hsi : (s : ℂ) = I
      · -- Case: s = i
        have h_gwn : HasGeneralizedWindingNumber γ (↑s : ℂ) (-1/2) := by
          rw [hsi, hγ_def]; exact (fdWindingDataFull_unconditional hH).winding_at_i
        rw [generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber γ hγ h_gwn,
            ← h_gwn.eq]
      · by_cases hsρ : (s : ℂ) = ellipticPointRho
        · have h_gwn : HasGeneralizedWindingNumber γ (↑s : ℂ) (-1/6) := by
            rw [hsρ, hγ_def]; exact (fdWindingDataFull_unconditional hH).winding_at_rho
          rw [generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber γ hγ h_gwn,
              ← h_gwn.eq]
        · by_cases hsρ1 : (s : ℂ) = ellipticPointRhoPlusOne
          · have h_gwn : HasGeneralizedWindingNumber γ (↑s : ℂ) (-1/6) := by
              rw [hsρ1, hγ_def]
              exact (fdWindingDataFull_unconditional hH).winding_at_rho_plus_one
            rw [generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber γ hγ h_gwn,
                ← h_gwn.eq]
          · -- Non-elliptic case: either strict interior or boundary
            by_cases hint : ‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2
            · -- Strict interior
              have h_gwn : HasGeneralizedWindingNumber γ (↑s : ℂ) (-1) := by
                rw [hγ_def]
                exact (fdWindingDataFull_unconditional hH).toFDWindingData.interior_winding
                  (↑s : ℂ) hint.1 hint.2 s.2 hs_im_lt
              rw [generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber γ hγ h_gwn,
                  ← h_gwn.eq]
            · -- On boundary (non-elliptic non-interior)
              have h_normSq : Complex.normSq (s : ℂ) ≥ 1 := hs_fd.1
              have h_gwn : HasGeneralizedWindingNumber γ (↑s : ℂ) (-1/2) := by
                rw [hγ_def]
                exact (fdWindingDataFull_unconditional hH).boundary_winding
                  (↑s : ℂ) s.2 hs_im_lt hsi hsρ hsρ1 hint h_normSq hs_fd.2
              rw [generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber γ hγ h_gwn,
                  ← h_gwn.eq]
    -- Sum equality follows
    have h_sum_eq :
        (∑ s ∈ S, generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ)) =
        ∑ s ∈ S, generalizedWindingNumber γ (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [h_gwn_eq s hs]
    -- Convert the limit value
    have h_F_eq : F_int_FM f S H = fun ε =>
      ∫ t in (0 : ℝ)..1,
        cpvIntegrandOn (sArcOfS S ∪ sVertOfS S)
          (logDeriv (modularFormCompOfComplex f)) γ.toPath.extend ε t := by
      funext ε
      simp only [F_int_FM, dif_pos hH, hγ_def]
    rw [h_F_eq, ← h_sum_eq]
    exact h_pv
  · -- Modular side: F_int → -(2πi * (k/12 - ord_cusp))
    intro H hH_ge hH
    have hH_ge_mod : H₀_mod ≤ H := le_trans hH₀_mod_le hH_ge
    set γ := (fdWindingDataFull_unconditional hH).boundary with hγ_def
    have hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t :=
      (fdWindingDataFull_unconditional hH).boundary_eq
    have h_pv := h_mod_bridge hH_ge_mod γ hγ
    refine h_pv.congr' ?_
    filter_upwards with ε
    simp only [F_int_FM, dif_pos hH, hγ_def]

end
