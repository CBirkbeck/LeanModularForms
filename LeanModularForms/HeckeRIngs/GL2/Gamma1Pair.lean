/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.Basic
import LeanModularForms.HeckeRIngs.GLn.SL2Surjection
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Hecke Pair for Γ₁(N)

Defines the submonoid `Δ₁(N)` and the Hecke pair `(Γ₁(N), Δ₁(N))` for the
congruence subgroup `Γ₁(N)`.

## Main definitions

* `Delta1_submonoid` — `Δ₁(N)`: integer 2×2 matrices with `a ≡ 1 (mod N)`,
  `c ≡ 0 (mod N)`, and positive determinant.
* `Gamma1_pair` — the Hecke pair `(Γ₁(N), Δ₁(N))`.

## Main results

* `Gamma1_le_Delta1` — `Γ₁(N) ≤ Δ₁(N)` as submonoids.
* `Delta1_le_commensurator` — `Δ₁(N) ≤ commensurator(Γ₁(N))`.

## References

* Miyake, *Modular Forms*, §4.5
* Diamond–Shurman, *A First Course in Modular Forms*, §5.1
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups ModularForm

namespace HeckeRing.GL2

/-- `Δ₁(N)`: integer 2×2 matrices with `a ≡ 1 (mod N)`, `c ≡ 0 (mod N)`,
and positive determinant. This pairs with `Γ₁(N)` to form a Hecke pair. -/
noncomputable def Delta1_submonoid (N : ℕ) : Submonoid (GL (Fin 2) ℚ) where
  carrier := {g | HasIntEntries 2 g ∧ 0 < (↑g : Matrix (Fin 2) (Fin 2) ℚ).det ∧
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
      (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧
      (N : ℤ) ∣ A 1 0 ∧ (A 0 0 : ZMod N) = 1}
  one_mem' := by
    refine ⟨hasIntEntries_one 2, by simp, 1, ?_, ?_, ?_⟩
    · ext i j; simp [map_apply, one_apply]
    · simp
    · simp
  mul_mem' := by
    intro a b ⟨ha, hda, A, hA, hAN, hAone⟩ ⟨hb, hdb, B, hB, hBN, hBone⟩
    refine ⟨HasIntEntries.mul (n := 2) ha hb,
      by simp only [GeneralLinearGroup.coe_mul, det_mul]; exact mul_pos hda hdb,
      A * B, ?_, ?_, ?_⟩
    · ext i j; simp [hA, hB, mul_apply, map_apply]
    · simp only [mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left hAN _) (dvd_mul_of_dvd_right hBN _)
    · simp only [mul_apply, Fin.sum_univ_two]
      have hB10 : (B 1 0 : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hBN
      simp [hAone, hBone, hB10]

/-- `Γ₁(N) ≤ Δ₁(N)`: the congruence subgroup embeds into the submonoid. -/
lemma Gamma1_le_Delta1 (N : ℕ) [NeZero N] :
    ((Gamma1 N).map (mapGL ℚ)).toSubmonoid ≤ Delta1_submonoid N := by
  intro g hg
  rw [Subgroup.mem_toSubmonoid, Subgroup.mem_map] at hg
  obtain ⟨σ, hσ_mem, rfl⟩ := hg
  rw [Gamma1_mem] at hσ_mem
  obtain ⟨ha, _, hc⟩ := hσ_mem
  have hmem : mapGL ℚ σ ∈ SLnZ_subgroup 2 := MonoidHom.mem_range.mpr ⟨σ, rfl⟩
  refine ⟨SLnZ_subgroup_hasIntEntries 2 hmem, ?_,
    (σ : Matrix (Fin 2) (Fin 2) ℤ), rfl,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc, ha⟩
  have hdet := σ.prop; rw [det_fin_two] at hdet
  simp only [det_fin_two, mapGL_coe_matrix, RingHom.mapMatrix_apply,
    map_apply_coe, algebraMap_int_eq, Int.coe_castRingHom, map_apply]
  exact_mod_cast hdet ▸ one_pos

private lemma Delta1_le_posDetInt (N : ℕ) :
    Delta1_submonoid N ≤ posDetInt_submonoid 2 := by
  intro g ⟨hint, hdet, _⟩
  exact ⟨hint, hdet⟩

private lemma Gamma1_map_commensurable_SLnZ (N : ℕ) [NeZero N] :
    Subgroup.Commensurable ((Gamma1 N).map (mapGL ℚ))
      (Subgroup.map (mapGL ℚ : SpecialLinearGroup (Fin 2) ℤ →* GL (Fin 2) ℚ) ⊤) := by
  constructor
  · rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
        Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  · rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
        Subgroup.relIndex_top_left]
    exact one_ne_zero

/-- `Δ₁(N) ≤ commensurator(Γ₁(N))`. The proof chains:
`Δ₁(N) ≤ posDetInt ≤ commensurator(SL₂(ℤ)) = commensurator(Γ₁(N))`,
where the last equality holds because `Γ₁(N)` has finite index in `SL₂(ℤ)`. -/
lemma Delta1_le_commensurator (N : ℕ) [NeZero N] :
    Delta1_submonoid N ≤
    (commensurator ((Gamma1 N).map (mapGL ℚ))).toSubmonoid := by
  rw [Subgroup.Commensurable.eq (Gamma1_map_commensurable_SLnZ N),
      ← MonoidHom.range_eq_map]
  exact (Delta1_le_posDetInt N).trans (posDetInt_le_commensurator 2)

/-- **The Hecke pair `(Γ₁(N), Δ₁(N))`** for level N.
This is the foundation for Hecke operators on `M_k(Γ₁(N))`. -/
noncomputable def Gamma1_pair (N : ℕ) [NeZero N] : HeckeRing.HeckePair (GL (Fin 2) ℚ) where
  H := (Gamma1 N).map (mapGL ℚ)
  Δ := Delta1_submonoid N
  h₀ := Gamma1_le_Delta1 N
  h₁ := Delta1_le_commensurator N

/-- The slash-action conjugation `σ` is the identity for matrices coming from
`SL₂(ℤ)`: their determinant is `1 > 0`, so the `σ` branch picks `RingHom.id ℂ`.
Replaces the inline `simp [UpperHalfPlane.σ, SpecialLinearGroup.mapGL]` idiom. -/
@[simp]
lemma σ_mapGL_real_eq_id (s : SL(2, ℤ)) :
    UpperHalfPlane.σ (mapGL ℝ s) = RingHom.id ℂ := by
  simp [UpperHalfPlane.σ, SpecialLinearGroup.mapGL]

/-! ### Normality of Γ₁(N) in Γ₀(N) and the diamond operator

`Gamma1(N)` is normal in `Gamma0(N)` because `Gamma1'(N) = ker(Gamma0Map N)` is
the kernel of a group homomorphism. This normality is the foundation for the
diamond operator `⟨d⟩` on modular forms for `Gamma1(N)`.
-/

open CongruenceSubgroup

/-- Conjugation by a `Gamma0(N)` element preserves `Gamma1(N)`.
This is the foundation for the diamond operator `⟨d⟩` on modular forms. -/
theorem Gamma0_normalizes_Gamma1 (g : ↥(Gamma0 N))
    (h : SL(2, ℤ)) (hh : h ∈ Gamma1 N) :
    (g : SL(2, ℤ)) * h * (g : SL(2, ℤ))⁻¹ ∈ Gamma1 N := by
  -- Embed h into Gamma0 N, check it's in Gamma1' = ker(Gamma0Map)
  set h₀ : ↥(Gamma0 N) := ⟨h, Gamma1_in_Gamma0 N hh⟩
  have hh1 : h₀ ∈ Gamma1' N := by
    rw [Gamma1_to_Gamma0_mem]; rwa [Gamma1_mem] at hh
  -- Kernel is normal: conjugation preserves Gamma1'
  have hconj : g * h₀ * g⁻¹ ∈ Gamma1' N :=
    (Gamma0Map N).normal_ker.conj_mem h₀ hh1 g
  -- Map back: Gamma1 = image of Gamma1' under Gamma0.subtype
  rw [Gamma1_mem]
  rwa [Gamma1_to_Gamma0_mem] at hconj

/-- `Gamma1(N)` is invariant under conjugation by `Gamma0(N)` as a subgroup
of `SL₂(ℤ)`. -/
theorem Gamma1_conjAct_eq (g : ↥(Gamma0 N)) :
    ConjAct.toConjAct (g : SL(2, ℤ)) • Gamma1 N = Gamma1 N := by
  ext h; constructor
  · rintro ⟨x, hx, rfl⟩; exact Gamma0_normalizes_Gamma1 g x hx
  · intro hh
    refine ⟨(g : SL(2, ℤ))⁻¹ * h * (g : SL(2, ℤ)), ?_, ?_⟩
    · show (g : SL(2, ℤ))⁻¹ * h * (g : SL(2, ℤ)) ∈ Gamma1 N
      have := Gamma0_normalizes_Gamma1
        ⟨(g : SL(2, ℤ))⁻¹, (Gamma0 N).inv_mem g.property⟩ h hh
      simpa [inv_inv] using this
    · simp [ConjAct.smul_def, mul_assoc]

/-- `Gamma1(N).map(mapGL ℝ)` is invariant under conjugation by `Gamma0(N)` elements
in `GL₂(ℝ)`. This is the subgroup-level equality needed for `ModularForm.translate`
to produce forms for the same level. -/
theorem Gamma1_map_conjAct_eq (g : ↥(Gamma0 N)) :
    ConjAct.toConjAct ((mapGL ℝ (g : SL(2, ℤ))))⁻¹ •
    (Gamma1 N).map (mapGL ℝ) = (Gamma1 N).map (mapGL ℝ) := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, map_inv, inv_inv, Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, hσy⟩
    have hmem : (g : SL(2, ℤ))⁻¹ * σ * (g : SL(2, ℤ)) ∈ Gamma1 N := by
      have := Gamma0_normalizes_Gamma1
        ⟨(g : SL(2, ℤ))⁻¹, (Gamma0 N).inv_mem g.property⟩ σ hσ
      simpa [inv_inv] using this
    exact ⟨_, hmem, by simp only [map_mul, map_inv]; rw [hσy]; group⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨(g : SL(2, ℤ)) * σ * (g : SL(2, ℤ))⁻¹,
      Gamma0_normalizes_Gamma1 g σ hσ, by simp [map_mul, map_inv]⟩

/-- Forward variant of `Gamma1_map_conjAct_eq`: `Gamma1(N).map(mapGL ℝ)` is invariant
under conjugation by `mapGL ℝ g` (rather than its inverse). Useful when the conjugation
appears in its non-inverted form (e.g. inside a `convert hc.smul ...`). -/
theorem Gamma1_map_conjAct_eq_forward (g : ↥(Gamma0 N)) :
    ConjAct.toConjAct (mapGL ℝ (g : SL(2, ℤ))) •
    (Gamma1 N).map (mapGL ℝ) = (Gamma1 N).map (mapGL ℝ) := by
  have := Gamma1_map_conjAct_eq ⟨(g : SL(2, ℤ))⁻¹, (Gamma0 N).inv_mem g.property⟩
  simpa [map_inv, ConjAct.toConjAct_inv, inv_inv, inv_smul_eq_iff] using this

/-- For a function `f` invariant under `Γ₁(N).map(mapGL ℝ)`, the slash action
`f ↦ f ∣[k] (mapGL ℝ g)` for `g ∈ Γ₀(N)` produces another `Γ₁(N).map(mapGL ℝ)`-invariant
function. This packages the slash-action half of the diamond-operator construction
shared by the modular and cusp-form variants, using normality of `Γ₁(N)` in `Γ₀(N)`. -/
lemma slash_mapGL_invariant_of_Gamma1_invariant {k : ℤ} (g : ↥(Gamma0 N))
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (Gamma1 N).map (mapGL ℝ), f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ (Gamma1 N).map (mapGL ℝ)) :
    (f ∣[k] mapGL ℝ (g : SL(2, ℤ))) ∣[k] γ = f ∣[k] mapGL ℝ (g : SL(2, ℤ)) := by
  rw [← SlashAction.slash_mul]
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
  rw [← map_mul, show (g : SL(2, ℤ)) * σ =
    ((g : SL(2, ℤ)) * σ * (g : SL(2, ℤ))⁻¹) * (g : SL(2, ℤ)) from by group,
    map_mul, SlashAction.slash_mul]
  exact congr_arg (· ∣[k] mapGL ℝ (g : SL(2, ℤ)))
    (hf _ (Subgroup.mem_map.mpr ⟨_, Gamma0_normalizes_Gamma1 g σ hσ, rfl⟩))

/-- For `g ∈ Γ₀(N)` and `γ ∈ GL₂(ℝ)` with `γ • ∞ = c`, a cusp `c` for `Γ₁(N).map(mapGL ℝ)`
transports along the conjugation by `mapGL ℝ g` to a cusp at `(mapGL ℝ g · γ) • ∞`.
This is the cusp-transport step shared between `diamondOpAux.bdd_at_cusps'` and
`diamondOpCuspAux.zero_at_cusps'`. -/
lemma isCusp_mul_mapGL_smul_infty (g : ↥(Gamma0 N))
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ)))
    {γ : GL (Fin 2) ℝ} (hγ : γ • (OnePoint.infty : OnePoint ℝ) = c) :
    IsCusp ((mapGL ℝ (g : SL(2, ℤ)) * γ) • (OnePoint.infty : OnePoint ℝ))
      ((Gamma1 N).map (mapGL ℝ)) := by
  have hmul : ((mapGL ℝ (g : SL(2, ℤ)) * γ) • (OnePoint.infty : OnePoint ℝ)) =
      (mapGL ℝ (g : SL(2, ℤ))) • (γ • (OnePoint.infty : OnePoint ℝ)) :=
    SemigroupAction.mul_smul (mapGL ℝ (g : SL(2, ℤ))) γ (OnePoint.infty : OnePoint ℝ)
  rw [hmul, hγ]
  exact (Gamma1_map_conjAct_eq_forward g) ▸ hc.smul (mapGL ℝ (g : SL(2, ℤ)))

/-- The diamond operator on modular forms for `Gamma1(N)`: for `g ∈ Gamma0(N)`,
the slash action `f ↦ f ∣[k] g` preserves `ModularForm ((Gamma1 N).map (mapGL ℝ)) k`
by the normality of `Gamma1` in `Gamma0`. Constructed directly to avoid dependent-type
casts from `ModularForm.translate`. -/
noncomputable def diamondOpAux (k : ℤ) (g : ↥(Gamma0 N)) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
      { toFun := ⇑f ∣[k] (mapGL ℝ (g : SL(2, ℤ)))
        slash_action_eq' _ hγ :=
          slash_mapGL_invariant_of_Gamma1_invariant g
            (fun _ hδ => SlashInvariantFormClass.slash_action_eq f _ hδ) hγ }
      holo' := (ModularFormClass.holo f).slash k _
      bdd_at_cusps' {c} hc _ hγ := by
        rw [← SlashAction.slash_mul, ← OnePoint.isBoundedAt_infty_iff,
          ← OnePoint.IsBoundedAt.smul_iff]
        exact ModularFormClass.bdd_at_cusps f (isCusp_mul_mapGL_smul_infty g hc hγ) }
  map_add' f₁ f₂ := by
    ext z; show ((⇑(f₁ + f₂)) ∣[k] mapGL ℝ (g : SL(2, ℤ))) z = _
    simp [SlashAction.add_slash, ModularForm.add_apply]; rfl
  map_smul' c f := by
    ext z; change ((c • ⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ))) z = c • _
    rw [ModularForm.smul_slash, σ_mapGL_real_eq_id]; rfl

/-- The `Gamma0Map` lifts to a group homomorphism to `(ZMod N)ˣ`: the bottom-right
entry is a unit mod N with inverse the top-left entry (from `det = 1` and `N ∣ c`). -/
noncomputable def Gamma0MapUnits : ↥(Gamma0 N) →* (ZMod N)ˣ where
  toFun g := by
    set A := (g : SL(2, ℤ)) with hA
    have hc : (A 1 0 : ZMod N) = 0 := Gamma0_mem.mp g.property
    have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      have := A.prop; rw [Matrix.det_fin_two] at this; linarith
    have hunit : (A 0 0 : ZMod N) * (A 1 1 : ZMod N) = 1 := by
      have := congr_arg (Int.cast : ℤ → ZMod N) hdet
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] at this
      exact this
    exact Units.mk (Gamma0Map N g) (A 0 0 : ZMod N)
      (by rw [mul_comm]; exact hunit) hunit
  map_one' := by ext; simp [Gamma0Map]
  map_mul' g₁ g₂ := by ext; exact map_mul (Gamma0Map N) g₁ g₂

@[simp]
lemma Gamma0MapUnits_val (g : ↥(Gamma0 N)) :
    (Gamma0MapUnits g : ZMod N) = Gamma0Map N g := rfl

/-- If two `Γ₀(N)` elements have equal image under `Gamma0Map`, their ratio
`g₁ · g₂⁻¹` lies in `Γ₁(N)` (as an `SL₂(ℤ)` element). This packages the kernel
computation `Gamma0Map (g₁ * g₂⁻¹) = 1` shared by the diamond-operator
well-definedness proofs (modular and cusp form variants). -/
lemma mul_inv_mem_Gamma1_of_Gamma0Map_eq (g₁ g₂ : ↥(Gamma0 N))
    (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    ((g₁ : SL(2, ℤ)) * (g₂ : SL(2, ℤ))⁻¹) ∈ Gamma1 N := by
  have hker : g₁ * g₂⁻¹ ∈ Gamma1' N := by
    show Gamma0Map N (g₁ * g₂⁻¹) = 1
    have heq_u : Gamma0MapUnits g₁ = Gamma0MapUnits g₂ := by ext; simp [heq]
    have h : Gamma0MapUnits (g₁ * g₂⁻¹) = 1 := by
      simp [map_mul, map_inv, heq_u, mul_inv_cancel]
    have := congr_arg Units.val h
    simp only [Gamma0MapUnits_val, Units.val_one] at this
    exact this
  rw [Gamma1_mem]; rwa [Gamma1_to_Gamma0_mem] at hker

/-- Slash-transport for `Γ₁(N)`-invariant functions: if `f` is invariant under
`(Γ₁(N)).map(mapGL ℝ)` and `Gamma0Map N g₁ = Gamma0Map N g₂`, then `f ∣[k] g₁ = f ∣[k] g₂`.
Packages the kernel computation (`mul_inv_mem_Gamma1_of_Gamma0Map_eq`) and the
`g₁ = (g₁g₂⁻¹) · g₂` decomposition shared by the diamond-operator well-definedness
proofs for modular and cusp forms. -/
lemma slash_eq_of_Gamma0Map_eq {k : ℤ} {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (Gamma1 N).map (mapGL ℝ), f ∣[k] γ = f)
    (g₁ g₂ : ↥(Gamma0 N)) (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    f ∣[k] mapGL ℝ (g₁ : SL(2, ℤ)) = f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ)) := by
  have hmem := mul_inv_mem_Gamma1_of_Gamma0Map_eq g₁ g₂ heq
  rw [show (g₁ : SL(2, ℤ)) = ((g₁ : SL(2, ℤ)) * (g₂ : SL(2, ℤ))⁻¹) *
    (g₂ : SL(2, ℤ)) from by group, map_mul, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩)]

/-- The diamond operator depends only on the `Gamma0Map` value: if two `Gamma0(N)`
elements have the same image, their diamond operators agree. -/
theorem diamondOpAux_eq_of_Gamma0Map_eq (k : ℤ) (g₁ g₂ : ↥(Gamma0 N))
    (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    diamondOpAux k g₁ = diamondOpAux k g₂ := by
  ext f z
  show (⇑f ∣[k] mapGL ℝ (g₁ : SL(2, ℤ))) z = (⇑f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ))) z
  rw [slash_eq_of_Gamma0Map_eq
    (fun _ hγ => SlashInvariantFormClass.slash_action_eq f _ hγ) g₁ g₂ heq]

/-! ### Public diamond operator indexed by `(ZMod N)ˣ` -/

/-- `Gamma0MapUnits` is surjective: every unit `d ∈ (ZMod N)ˣ` is realized as the
bottom-right entry of some `g ∈ Gamma0(N)`. The proof lifts the diagonal matrix
`diag(d⁻¹, d)` from `SL₂(ZMod N)` to `SL₂(ℤ)` via `SL2_reduction_surjective`. -/
theorem Gamma0MapUnits_surjective [NeZero N] :
    Function.Surjective (Gamma0MapUnits (N := N)) := by
  intro d
  set target : SpecialLinearGroup (Fin 2) (ZMod N) :=
    ⟨!![↑d⁻¹, 0; 0, ↑d], by simp [Matrix.det_fin_two]⟩
  obtain ⟨g, hg⟩ := SL2Reduction.SL2_reduction_surjective N target
  have hg0 : g ∈ Gamma0 N := by
    rw [Gamma0_mem]
    have := congr_fun (congr_fun (congr_arg Subtype.val hg) 1) 0
    simp at this; exact this
  refine ⟨⟨g, hg0⟩, ?_⟩
  ext; show Gamma0Map N ⟨g, hg0⟩ = ↑d
  simp only [Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
  have := congr_fun (congr_fun (congr_arg Subtype.val hg) 1) 1
  simp at this; exact this

/-- The diamond operator `⟨d⟩` on modular forms for `Gamma1(N)`, indexed by
`d : (ZMod N)ˣ`. Defined by choosing a representative `g ∈ Gamma0(N)` with
`Gamma0MapUnits g = d` and applying `diamondOpAux`. Well-defined by
`diamondOpAux_eq_of_Gamma0Map_eq`. -/
noncomputable def diamondOp [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  diamondOpAux k (Gamma0MapUnits_surjective d).choose

/-- `diamondOp` equals `diamondOpAux` on any representative with the right image. -/
theorem diamondOp_eq_diamondOpAux [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : Gamma0MapUnits g = d) :
    diamondOp k d = diamondOpAux k g :=
  diamondOpAux_eq_of_Gamma0Map_eq k _ g
    (by simp [← Gamma0MapUnits_val, (Gamma0MapUnits_surjective d).choose_spec, hg])

/-- The diamond operator at `1` is the identity. -/
@[simp]
theorem diamondOp_one [NeZero N] (k : ℤ) : diamondOp (N := N) k 1 = LinearMap.id := by
  rw [diamondOp_eq_diamondOpAux k 1 1 (map_one _)]
  ext f z; show (⇑f ∣[k] mapGL ℝ (1 : SL(2, ℤ))) z = f z
  simp [map_one, SlashAction.slash_one]

/-- Diamond operators compose: `⟨d₁ * d₂⟩ = ⟨d₁⟩ ∘ ⟨d₂⟩`. Uses commutativity
of `(ZMod N)ˣ` to absorb the order reversal from `SlashAction.slash_mul`. -/
theorem diamondOp_mul [NeZero N] (k : ℤ) (d₁ d₂ : (ZMod N)ˣ) :
    diamondOp k (d₁ * d₂) = (diamondOp k d₁).comp (diamondOp k d₂) := by
  obtain ⟨g₁, hg₁⟩ := Gamma0MapUnits_surjective (N := N) d₁
  obtain ⟨g₂, hg₂⟩ := Gamma0MapUnits_surjective (N := N) d₂
  rw [diamondOp_eq_diamondOpAux k (d₁ * d₂) (g₂ * g₁)
      (by simp [map_mul, hg₁, hg₂, mul_comm]),
    diamondOp_eq_diamondOpAux k d₁ g₁ hg₁,
    diamondOp_eq_diamondOpAux k d₂ g₂ hg₂]
  ext f z; show (⇑f ∣[k] mapGL ℝ ((g₂ : SL(2, ℤ)) * (g₁ : SL(2, ℤ)))) z =
    ((⇑f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ))) ∣[k] mapGL ℝ (g₁ : SL(2, ℤ))) z
  rw [map_mul, SlashAction.slash_mul]

/-- The diamond operator as a monoid homomorphism `(ZMod N)ˣ →* Module.End ℂ (...)`.
Commutativity of `(ZMod N)ˣ` absorbs the order reversal from slash multiplication. -/
noncomputable def diamondOpHom [NeZero N] (k : ℤ) :
    (ZMod N)ˣ →* Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := diamondOp k
  map_one' := diamondOp_one k
  map_mul' := diamondOp_mul k

/-! ### Diamond operator on cusp forms -/

/-- Diamond operator restricted to cusp forms for `Gamma1(N)`. Same construction
as `diamondOpAux` but preserving the cusp vanishing condition. -/
private noncomputable def diamondOpCuspAux (k : ℤ) (g : ↥(Gamma0 N)) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
      { toFun := ⇑f ∣[k] (mapGL ℝ (g : SL(2, ℤ)))
        slash_action_eq' _ hγ :=
          slash_mapGL_invariant_of_Gamma1_invariant g
            (fun _ hδ => SlashInvariantFormClass.slash_action_eq f _ hδ) hγ }
      holo' := (CuspFormClass.holo f).slash k _
      zero_at_cusps' {c} hc _ hγ := by
        rw [← SlashAction.slash_mul, ← OnePoint.isZeroAt_infty_iff,
          ← OnePoint.IsZeroAt.smul_iff]
        exact CuspFormClass.zero_at_cusps f (isCusp_mul_mapGL_smul_infty g hc hγ) }
  map_add' f₁ f₂ := by
    ext z; show ((⇑(f₁ + f₂)) ∣[k] mapGL ℝ (g : SL(2, ℤ))) z = _
    simp [SlashAction.add_slash, CuspForm.add_apply]; rfl
  map_smul' c f := by
    ext z; change ((c • ⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ))) z = c • _
    rw [ModularForm.smul_slash, σ_mapGL_real_eq_id]; rfl

/-- Well-definedness for cusp-form diamond operator (same proof as `ModularForm` version). -/
theorem diamondOpCuspAux_eq_of_Gamma0Map_eq (k : ℤ) (g₁ g₂ : ↥(Gamma0 N))
    (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    diamondOpCuspAux k g₁ = diamondOpCuspAux k g₂ := by
  ext f z
  show (⇑f ∣[k] mapGL ℝ (g₁ : SL(2, ℤ))) z = (⇑f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ))) z
  rw [slash_eq_of_Gamma0Map_eq
    (fun _ hγ => SlashInvariantFormClass.slash_action_eq f _ hγ) g₁ g₂ heq]

/-- The cusp-form diamond operator indexed by `d : (ZMod N)ˣ`. -/
noncomputable def diamondOpCusp [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  diamondOpCuspAux k (Gamma0MapUnits_surjective d).choose

/-- `diamondOpCusp` equals `diamondOpCuspAux` on any representative. -/
theorem diamondOpCusp_eq (k : ℤ) (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : Gamma0MapUnits g = d) [NeZero N] :
    diamondOpCusp k d = diamondOpCuspAux k g :=
  diamondOpCuspAux_eq_of_Gamma0Map_eq k _ g
    (by simp [← Gamma0MapUnits_val, (Gamma0MapUnits_surjective d).choose_spec, hg])

@[simp]
theorem diamondOpCusp_one [NeZero N] (k : ℤ) :
    diamondOpCusp (N := N) k 1 = LinearMap.id := by
  rw [diamondOpCusp_eq k 1 1 (map_one _)]
  ext f z; show (⇑f ∣[k] mapGL ℝ (1 : SL(2, ℤ))) z = f z
  simp [map_one, SlashAction.slash_one]

theorem diamondOpCusp_mul [NeZero N] (k : ℤ) (d₁ d₂ : (ZMod N)ˣ) :
    diamondOpCusp k (d₁ * d₂) = (diamondOpCusp k d₁).comp (diamondOpCusp k d₂) := by
  obtain ⟨g₁, hg₁⟩ := Gamma0MapUnits_surjective (N := N) d₁
  obtain ⟨g₂, hg₂⟩ := Gamma0MapUnits_surjective (N := N) d₂
  rw [diamondOpCusp_eq k (d₁ * d₂) (g₂ * g₁) (by simp [map_mul, hg₁, hg₂, mul_comm]),
    diamondOpCusp_eq k d₁ g₁ hg₁, diamondOpCusp_eq k d₂ g₂ hg₂]
  ext f z; show (⇑f ∣[k] mapGL ℝ ((g₂ : SL(2, ℤ)) * (g₁ : SL(2, ℤ)))) z =
    ((⇑f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ))) ∣[k] mapGL ℝ (g₁ : SL(2, ℤ))) z
  rw [map_mul, SlashAction.slash_mul]

/-- The cusp-form diamond operator as a monoid homomorphism. -/
noncomputable def diamondOpCuspHom [NeZero N] (k : ℤ) :
    (ZMod N)ˣ →* Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := diamondOpCusp k
  map_one' := diamondOpCusp_one k
  map_mul' := diamondOpCusp_mul k

/-! ### Nebentypus character spaces

The `χ`-eigenspace of the diamond operators: cusp forms `f` with `⟨d⟩ f = χ(d) • f`
for all `d ∈ (ZMod N)ˣ`. Defined as a joint eigenspace using mathlib's
`Module.End.eigenspace`. -/

/-- The Nebentypus character space `S_k(Γ₁(N), χ)`: cusp forms on which every
diamond operator `⟨d⟩` acts by the scalar `χ(d)`. -/
noncomputable def cuspFormCharSpace [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, Module.End.eigenspace (diamondOpCuspHom k d) (↑(χ d))

/-- Membership in `S_k(Γ₁(N), χ)`: `f` is in the `χ`-eigenspace iff
`⟨d⟩ f = χ(d) • f` for every `d ∈ (ZMod N)ˣ`. -/
theorem mem_cuspFormCharSpace_iff [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspFormCharSpace k χ ↔
    ∀ d : (ZMod N)ˣ, diamondOpCuspHom k d f = (↑(χ d) : ℂ) • f := by
  simp [cuspFormCharSpace, Submodule.mem_iInf]

/-- Diamond operators act by `χ(d)` on elements of `S_k(Γ₁(N), χ)`. -/
theorem diamondOpCusp_apply_charSpace [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (d : (ZMod N)ˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) :
    diamondOpCuspHom k d f = (↑(χ d) : ℂ) • f :=
  ((mem_cuspFormCharSpace_iff k χ f).mp hf) d

/-- The modular-form Nebentypus character space `M_k(Γ₁(N), χ)`. -/
noncomputable def modFormCharSpace [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, Module.End.eigenspace (diamondOpHom k d) (↑(χ d))

theorem mem_modFormCharSpace_iff [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ modFormCharSpace k χ ↔
    ∀ d : (ZMod N)ˣ, diamondOpHom k d f = (↑(χ d) : ℂ) • f := by
  simp [modFormCharSpace, Submodule.mem_iInf]

/-! ### Twisted slash action and Nebentypus invariance

The character-twisted slash action `twistedSlash k χ g f = (χ g)⁻¹ • (f ∣[k] g)` on
functions `f : ℍ → ℂ`, where `χ : Gamma0 N →* ℂˣ`. Fixed points satisfy the
Nebentypus relation `f ∣[k] g = χ(g) • f`. -/

/-- The character-twisted slash action: `(χ(g))⁻¹ • (f ∣[k] g)`.
Fixed points are exactly forms satisfying `f ∣[k] g = χ(g) • f`. -/
noncomputable def twistedSlash (k : ℤ) (χ : ↥(Gamma0 N) →* ℂˣ)
    (g : ↥(Gamma0 N)) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  (↑(χ g) : ℂ)⁻¹ • (f ∣[k] mapGL ℝ (g : SL(2, ℤ)))

/-- The twisted slash at `1` is the identity. -/
@[simp]
theorem twistedSlash_one (k : ℤ) (χ : ↥(Gamma0 N) →* ℂˣ) (f : UpperHalfPlane → ℂ) :
    twistedSlash k χ 1 f = f := by
  simp [twistedSlash, map_one, Units.val_one, SlashAction.slash_one]

/-- The Nebentypus invariance predicate: `f` is a fixed point of the twisted slash
for all `g ∈ Gamma0(N)`. -/
def IsNebentypus (k : ℤ) (χ : ↥(Gamma0 N) →* ℂˣ) (f : UpperHalfPlane → ℂ) : Prop :=
  ∀ g : ↥(Gamma0 N), twistedSlash k χ g f = f

/-- `IsNebentypus` is equivalent to the classical Nebentypus relation
`f ∣[k] g = χ(g) • f` for all `g ∈ Gamma0(N)`. -/
theorem isNebentypus_iff (k : ℤ) (χ : ↥(Gamma0 N) →* ℂˣ) (f : UpperHalfPlane → ℂ) :
    IsNebentypus k χ f ↔
    ∀ g : ↥(Gamma0 N), f ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ g) : ℂ) • f := by
  simp only [IsNebentypus, twistedSlash]
  constructor
  · intro h g
    have := h g -- (χ g)⁻¹ • (f ∣[k] g) = f
    calc f ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ g) : ℂ) • ((↑(χ g) : ℂ)⁻¹ •
        (f ∣[k] mapGL ℝ (g : SL(2, ℤ)))) := by
          rw [smul_smul, mul_inv_cancel₀ (χ g).ne_zero, one_smul]
      _ = _ := by rw [this]
  · intro h g
    rw [show f ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ g) : ℂ) • f from h g]
    rw [smul_smul, inv_mul_cancel₀ (χ g).ne_zero, one_smul]

/-- The twisted slash is multiplicative on `Gamma1`-invariant functions. Uses
commutativity of `(ZMod N)ˣ` (via `Gamma0MapUnits`) to absorb the order reversal
from `SlashAction.slash_mul`, and the commutator `[g₁,g₂] ∈ Gamma1` to
equate `f ∣[k] (g₁g₂)` with `f ∣[k] (g₂g₁)`. -/
theorem twistedSlash_mul {k : ℤ} {χ : ↥(Gamma0 N) →* ℂˣ}
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (Gamma1 N).map (mapGL ℝ), f ∣[k] γ = f)
    (g₁ g₂ : ↥(Gamma0 N)) :
    twistedSlash k χ (g₁ * g₂) f = twistedSlash k χ g₁ (twistedSlash k χ g₂ f) := by
  simp only [twistedSlash, map_mul, Units.val_mul]
  -- Pull scalar through slash on RHS, then combine nested smuls
  rw [ModularForm.smul_slash, σ_mapGL_real_eq_id, RingHom.id_apply, smul_smul]
  -- Prove and apply scalar identity separately
  have hscalar : (↑(χ g₁) * ↑(χ g₂) : ℂ)⁻¹ = (↑(χ g₁) : ℂ)⁻¹ * (↑(χ g₂) : ℂ)⁻¹ := by
    rw [_root_.mul_inv_rev, mul_comm]
  rw [hscalar]
  -- Scalars now match; reduce to slash equality via congr
  congr 1
  -- Commutator c₀ = g₁g₂g₁⁻¹g₂⁻¹ in Gamma0 subtype (so map_mul/map_inv fire)
  set c₀ := g₁ * g₂ * g₁⁻¹ * g₂⁻¹
  -- Gamma0MapUnits maps commutator to 1 (abelian target)
  have hc₀_units : Gamma0MapUnits c₀ = 1 := by
    show Gamma0MapUnits (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = 1
    simp [map_mul, map_inv]
  -- So c₀ ∈ Gamma1' N, hence ↑c₀ ∈ Gamma1 N
  have hc₀_gamma1 : (c₀ : SL(2, ℤ)) ∈ Gamma1 N := by
    rw [Gamma1_mem]
    exact (Gamma1_to_Gamma0_mem c₀).mp
      (Gamma1_mem'.mpr (by rw [← Gamma0MapUnits_val, hc₀_units, Units.val_one]))
  -- Factor g₁g₂ = c₀ * g₂g₁
  have hfact : ((g₁ * g₂ : ↥(Gamma0 N)) : SL(2, ℤ)) =
      (c₀ : SL(2, ℤ)) * ((g₂ : SL(2, ℤ)) * (g₁ : SL(2, ℤ))) := by
    show (↑g₁ : SL(2, ℤ)) * ↑g₂ =
      (↑g₁ * ↑g₂ * (↑g₁)⁻¹ * (↑g₂)⁻¹ : SL(2, ℤ)) * (↑g₂ * ↑g₁)
    group
  rw [hfact, map_mul, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map.mpr ⟨_, hc₀_gamma1, rfl⟩),
    map_mul, SlashAction.slash_mul]

/-- For the trivial character, `twistedSlash` reduces to the ordinary slash action. -/
theorem twistedSlash_trivial (k : ℤ) (g : ↥(Gamma0 N))
    (f : UpperHalfPlane → ℂ) :
    twistedSlash k (1 : ↥(Gamma0 N) →* ℂˣ) g f =
    f ∣[k] mapGL ℝ (g : SL(2, ℤ)) := by
  simp [twistedSlash, MonoidHom.one_apply, Units.val_one]

/-- **Bridge**: for a `Gamma1`-invariant modular form `f`, membership in the
diamond-eigenspace `modFormCharSpace k χ₀` is equivalent to twisted-slash
invariance under `χ₀ ∘ Gamma0MapUnits`. -/
theorem modFormCharSpace_iff_nebentypus [NeZero N] (k : ℤ) (χ₀ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ modFormCharSpace k χ₀ ↔
    ∀ g : ↥(Gamma0 N), (⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
      (↑(χ₀ (Gamma0MapUnits g)) : ℂ) • ⇑f := by
  rw [mem_modFormCharSpace_iff]
  constructor
  · intro h g
    -- h says: ∀ d, diamondOp k d f = χ₀(d) • f (diamondOpHom k d = diamondOp k d)
    -- For d = Gamma0MapUnits g: diamondOp k d = diamondOpAux k g
    have hd := h (Gamma0MapUnits g)
    -- diamondOpHom k d f = diamondOp k d f, and diamondOp k d = diamondOpAux k g
    show (⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ₀ (Gamma0MapUnits g)) : ℂ) • ⇑f
    rw [show diamondOpHom k (Gamma0MapUnits g) = diamondOp k (Gamma0MapUnits g) from rfl,
        diamondOp_eq_diamondOpAux k _ g rfl] at hd
    -- hd : diamondOpAux k g f = χ₀(Gamma0MapUnits g) • f (as ModularForm)
    -- Need: ⇑f ∣[k] g = χ₀(Gamma0MapUnits g) • ⇑f (as functions)
    exact congr_arg (⇑· : ModularForm _ k → _) hd
  · intro h d
    obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective (N := N) d
    show diamondOp k d f = (↑(χ₀ d) : ℂ) • f
    rw [diamondOp_eq_diamondOpAux k d g hg, ← hg]
    exact ModularForm.ext (congr_fun (h g))

/-- **Bridge (cusp forms)**: for a `Gamma1`-invariant cusp form `f`, membership in the
diamond-eigenspace `cuspFormCharSpace k χ₀` is equivalent to twisted-slash
invariance under `χ₀ ∘ Gamma0MapUnits`. -/
theorem cuspFormCharSpace_iff_nebentypus [NeZero N] (k : ℤ) (χ₀ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspFormCharSpace k χ₀ ↔
    ∀ g : ↥(Gamma0 N), (⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
      (↑(χ₀ (Gamma0MapUnits g)) : ℂ) • ⇑f := by
  rw [mem_cuspFormCharSpace_iff]
  constructor
  · intro h g
    have hd := h (Gamma0MapUnits g)
    show (⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ₀ (Gamma0MapUnits g)) : ℂ) • ⇑f
    rw [show diamondOpCuspHom k (Gamma0MapUnits g) = diamondOpCusp k (Gamma0MapUnits g) from rfl,
        diamondOpCusp_eq k _ g rfl] at hd
    exact congr_arg (⇑· : CuspForm _ k → _) hd
  · intro h d
    obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective (N := N) d
    show diamondOpCusp k d f = (↑(χ₀ d) : ℂ) • f
    rw [diamondOpCusp_eq k d g hg, ← hg]
    exact CuspForm.ext (congr_fun (h g))

/-- Membership in `M_k(Γ₁(N), 1)` (trivial character) is equivalent to ordinary
`Γ₀(N)` slash-invariance on the underlying function. -/
theorem mem_modFormCharSpace_trivial_iff [NeZero N] (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ modFormCharSpace k 1 ↔
    ∀ g : ↥(Gamma0 N), (⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) = ⇑f := by
  rw [modFormCharSpace_iff_nebentypus]
  simp [MonoidHom.one_apply, Units.val_one]

/-- Membership in `S_k(Γ₁(N), 1)` (trivial character) is equivalent to ordinary
`Γ₀(N)` slash-invariance on the underlying function. -/
theorem mem_cuspFormCharSpace_trivial_iff [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspFormCharSpace k 1 ↔
    ∀ g : ↥(Gamma0 N), (⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) = ⇑f := by
  rw [cuspFormCharSpace_iff_nebentypus]
  simp [MonoidHom.one_apply, Units.val_one]

end HeckeRing.GL2
