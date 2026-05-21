module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

@[expose] public section

/-
Probably put this at Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean
-/

open UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm UpperHalfPlane

lemma Filter.eventually_atImInfty {p : ℍ → Prop} :
    (∀ᶠ x in atImInfty, p x) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z :=
  atImInfty_mem (setOf p)

lemma Filter.tendsto_im_atImInfty : Tendsto (fun x : ℍ ↦ x.im) atImInfty atTop :=
  tendsto_iff_comap.mpr fun ⦃_⦄ a => a

/-- If f tends to c ≠ 0 at infinity, then f ≠ 0 as a function.

This packages the common argument: if f = 0, then f → 0, but also f → c by hypothesis.
By uniqueness of limits, 0 = c, contradicting c ≠ 0. -/
lemma ne_zero_of_tendsto_ne_zero {f : ℍ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hf : Tendsto f atImInfty (nhds c)) : f ≠ 0 := fun h =>
  hc (tendsto_nhds_unique tendsto_const_nhds (h ▸ hf)).symm

theorem zero_at_cusps_of_zero_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {k : ℤ}
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic]
    (hc : IsCusp c 𝒢) (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsZeroAtImInfty (f ∣[k] A)) :
    c.IsZeroAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  refine (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun A hA ↦ hb A ⟨A, rfl⟩

theorem bounded_at_cusps_of_bounded_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {k : ℤ}
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic]
    (hc : IsCusp c 𝒢) (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsBoundedAtImInfty (f ∣[k] A)) :
    c.IsBoundedAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  exact (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun A hA ↦ hb A ⟨A, rfl⟩
