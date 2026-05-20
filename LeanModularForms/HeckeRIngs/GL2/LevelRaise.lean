/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import Mathlib.Analysis.Complex.Periodic
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Level-raising operator for cusp forms (Miyake §4.6 Lemma 4.6.1)

This file extracts the level-raising machinery from `Newforms.lean` so that
downstream theory (notably `Eigenforms/ConductorTheorem.lean`) can depend on
just this lightweight file rather than pulling the entire `Newforms.lean`
infrastructure (which transitively depends on `AdjointTheory.lean` /
`BlockBijection.lean`).

The level-raising operator `ι_d : S_k(Γ₁(M)) → S_k(Γ₁(d·M))` sends a cusp
form `f` for `Γ₁(M)` to the cusp form `(ι_d f)(τ) = f(d·τ)` for the deeper
level `Γ₁(d·M)`, normalised so that the Fourier coefficient at `q^d`
equals the Fourier coefficient of `f` at `q`. In matrix form:
`ι_d f = d^{1-k} · (f ∣[k] [[d,0],[0,1]])`.

## Main definitions

* `levelRaiseMatrix d` — the matrix `α_d = [[d, 0], [0, 1]]` in `GL(2, ℝ)`.
* `levelRaiseFun d k f` — the level-raising operator at the function level.
* `levelRaiseConjOfDvd d γ hdvd` — the explicit `SL(2, ℤ)` element
  `α_d γ α_d⁻¹` constructed when `d ∣ γ.val 1 0`.
* `levelRaiseConj d M γ hγ` — specialisation of `levelRaiseConjOfDvd` to
  `γ ∈ Γ₁(d·M)` (where the divisibility is automatic).
* `CuspForm.restrictSubgroup` — restriction of a cusp form along a subgroup
  inclusion `Γ' ≤ Γ`.
* `levelRaise M d k` — the bundled `ℂ`-linear level-raising operator
  `S_k(Γ₁(M)) →ₗ[ℂ] S_k(Γ₁(d·M))`.

## References

* Miyake, *Modular Forms*, §4.6 (Lemma 4.6.1, p.162).
* Diamond–Shurman, *A First Course in Modular Forms*, §5.7 (DS (5.16)).
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup CuspForm ModularFormClass

open scoped MatrixGroups ModularForm Pointwise

noncomputable section

namespace HeckeRing.GL2

/-! ### The level-raising matrix `α_d` and function-level operator `ι_d` -/

/-- The level-raising matrix `α_d = [[d, 0], [0, 1]]` in `GL(2, ℝ)`. -/
def levelRaiseMatrix (d : ℕ) [NeZero d] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(d : ℝ), 0; 0, 1]
    (by simp [Matrix.det_fin_two, Nat.cast_ne_zero.mpr (NeZero.ne d)])

/-- The level-raising operator at the FUNCTION level: `(ι_d f)(τ) = f(d·τ)`.

In matrix form: `f ∣[k] [[d,0],[0,1]] · d^{(k-1)/?}`. Mathlib's slash action
includes a `det^(k-1)` factor for GL₂(ℝ) elements, so the formula is:
`(f ∣[k] α_d)(τ) = d^{k-1} · 1^{-k} · σ(α_d)(f(α_d · τ)) = d^{k-1} · f(d·τ)`.

The level-raising `ι_d` removes the `d^{k-1}` to get `f(d·τ)`:
`ι_d f = d^{1-k} · (f ∣[k] α_d)`. -/
def levelRaiseFun (d : ℕ) [NeZero d] (k : ℤ) (f : UpperHalfPlane → ℂ) :
    UpperHalfPlane → ℂ :=
  ((d : ℂ) ^ (1 - k)) • (f ∣[k] levelRaiseMatrix d)

/-! ### The δ_d conjugation (Miyake Lemma 4.6.1)

For γ ∈ Γ₁(d*M), the conjugation `δ_d * γ * δ_d⁻¹` (where `δ_d = [[d, 0], [0, 1]]`)
gives an element of Γ₁(M). The explicit formula is:

  γ = [[a, b], [c, e]]    →    δ_d γ δ_d⁻¹ = [[a, d*b], [c/d, e]]

This is the key matrix calculation for the level-raising operator. -/

/-- For γ ∈ Γ₁(d*M), the entry `γ.val 1 0` is divisible by `d`. -/
lemma Gamma1_dmul_lower_left_dvd (d M : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 (d * M)) :
    (d : ℤ) ∣ γ.val 1 0 := by
  rw [Gamma1_mem] at hγ
  obtain ⟨_, _, hc⟩ := hγ
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
  exact dvd_trans ⟨M, by push_cast; ring⟩ h

/-- For `γ ∈ Γ₀(d*M)`, the entry `γ.val 1 0` is divisible by `d`. -/
lemma Gamma0_dmul_lower_left_dvd (d M : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (d * M)) :
    (d : ℤ) ∣ γ.val 1 0 := by
  rw [Gamma0_mem] at hγ
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  exact dvd_trans ⟨M, by push_cast; ring⟩ h

/-- Construction of `δ_d γ δ_d⁻¹` as an explicit `SL(2, ℤ)` element when
`d ∣ γ.val 1 0`. The formula `[[a, d*b], [c/d, e]]` is integer by hypothesis. -/
noncomputable def levelRaiseConjOfDvd (d : ℕ) [NeZero d]
    (γ : SL(2, ℤ)) (hdvd : (d : ℤ) ∣ γ.val 1 0) : SL(2, ℤ) := by
  refine ⟨!![γ.val 0 0, d * γ.val 0 1;
             γ.val 1 0 / d, γ.val 1 1], ?_⟩
  have hdet : γ.val.det = 1 := γ.property
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.det_fin_two_of]
  have h_calc : (d : ℤ) * γ.val 0 1 * (γ.val 1 0 / d) = γ.val 0 1 * γ.val 1 0 := by
    rw [show (d : ℤ) * γ.val 0 1 * (γ.val 1 0 / d) =
        γ.val 0 1 * ((γ.val 1 0 / d) * d) from by ring]
    rw [Int.ediv_mul_cancel hdvd]
  linarith [hdet]

/-- Construction of `δ_d γ δ_d⁻¹` as an explicit `SL(2, ℤ)` element when
`γ ∈ Γ₁(d*M)`. The formula `[[a, d*b], [c/d, e]]` is integer because `d ∣ c`. -/
noncomputable def levelRaiseConj (d M : ℕ) [NeZero d]
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 (d * M)) : SL(2, ℤ) :=
  levelRaiseConjOfDvd d γ (Gamma1_dmul_lower_left_dvd d M γ hγ)

/-- The conjugated matrix is in `Γ₀(M)` when `γ ∈ Γ₀(d*M)`. The (1,0) entry of
`δ_d γ δ_d⁻¹` is `c/d`, which is divisible by `M` because `c` is divisible by `d*M`. -/
lemma levelRaiseConjOfDvd_mem_Gamma0 (d M : ℕ) [NeZero d]
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (d * M)) :
    levelRaiseConjOfDvd d γ (Gamma0_dmul_lower_left_dvd d M γ hγ) ∈ Gamma0 M := by
  rw [Gamma0_mem]
  -- (1,0) entry of conjugate is γ.val 1 0 / d
  have h_eq : ((levelRaiseConjOfDvd d γ
      (Gamma0_dmul_lower_left_dvd d M γ hγ)).val 1 0 : ℤ) = γ.val 1 0 / d := rfl
  show (((levelRaiseConjOfDvd d γ
    (Gamma0_dmul_lower_left_dvd d M γ hγ)).val 1 0 : ℤ) : ZMod M) = 0
  rw [h_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [Gamma0_mem] at hγ
  have hdvd_dM : ((d * M : ℕ) : ℤ) ∣ γ.val 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  obtain ⟨j, hj⟩ := hdvd_dM
  refine ⟨j, ?_⟩
  have hd_ne : (d : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [hj]
  push_cast
  rw [show (d : ℤ) * ↑M * j = (d : ℤ) * (M * j) from by ring,
    Int.mul_ediv_cancel_left _ hd_ne]

/-- The (1,1) entry of the conjugate equals the (1,1) entry of the original. -/
lemma levelRaiseConjOfDvd_lower_right (d : ℕ) [NeZero d]
    (γ : SL(2, ℤ)) (hdvd : (d : ℤ) ∣ γ.val 1 0) :
    (levelRaiseConjOfDvd d γ hdvd).val 1 1 = γ.val 1 1 := rfl

/-- The matrix conjugation identity (in `GL(2, ℝ)`) for `levelRaiseConjOfDvd`:
`α_d * γ * α_d⁻¹ = (levelRaiseConjOfDvd d γ hdvd : GL₂(ℝ))`, equivalently
`levelRaiseMatrix d * mapGL ℝ γ = mapGL ℝ (levelRaiseConjOfDvd d γ hdvd) * levelRaiseMatrix d`. -/
lemma levelRaiseMatrix_mul_mapGL (d : ℕ) [NeZero d]
    (γ : SL(2, ℤ)) (hdvd : (d : ℤ) ∣ γ.val 1 0) :
    mapGL ℝ (levelRaiseConjOfDvd d γ hdvd) * levelRaiseMatrix d =
      levelRaiseMatrix d * mapGL ℝ γ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.mul_apply, Fin.sum_univ_two]
  have hdvd_real : ((d : ℕ) : ℝ) * (((γ.val 1 0 / (d : ℤ)) : ℤ) : ℝ) = ((γ.val 1 0 : ℤ) : ℝ) := by
    rw [mul_comm, ← Int.cast_natCast (R := ℝ), ← Int.cast_mul, Int.ediv_mul_cancel hdvd]
  fin_cases i <;> fin_cases j <;>
    simp [levelRaiseMatrix, levelRaiseConjOfDvd, mul_comm, hdvd_real]

/-- The conjugated matrix is in `Γ₁(M)` (Miyake Lemma 4.6.1, conjugation step).

If `γ ∈ Γ₁(d*M)` then `δ_d γ δ_d⁻¹ ∈ Γ₁(M)`. -/
lemma levelRaiseConj_mem_Gamma1 (d M : ℕ) [NeZero d]
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 (d * M)) :
    levelRaiseConj d M γ hγ ∈ Gamma1 M := by
  obtain ⟨ha, he, hc⟩ := (Gamma1_mem _ _).mp hγ
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · -- (0,0) entry of conjugate is γ.val 0 0
    have h_eq : ((levelRaiseConj d M γ hγ).val 0 0 : ℤ) = γ.val 0 0 := rfl
    show (((levelRaiseConj d M γ hγ).val 0 0 : ℤ) : ZMod M) = 1
    rw [h_eq]
    have := congr_arg (ZMod.castHom (Nat.dvd_mul_left M d) (ZMod M)) ha
    simpa using this
  · -- (1,1) entry of conjugate is γ.val 1 1
    have h_eq : ((levelRaiseConj d M γ hγ).val 1 1 : ℤ) = γ.val 1 1 := rfl
    show (((levelRaiseConj d M γ hγ).val 1 1 : ℤ) : ZMod M) = 1
    rw [h_eq]
    have := congr_arg (ZMod.castHom (Nat.dvd_mul_left M d) (ZMod M)) he
    simpa using this
  · -- (1,0) entry of conjugate is γ.val 1 0 / d, which is M * (something)
    have h_eq : ((levelRaiseConj d M γ hγ).val 1 0 : ℤ) = γ.val 1 0 / d := rfl
    show (((levelRaiseConj d M γ hγ).val 1 0 : ℤ) : ZMod M) = 0
    rw [h_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hdvd_dM : ((d * M : ℕ) : ℤ) ∣ γ.val 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
    obtain ⟨j, hj⟩ := hdvd_dM
    refine ⟨j, ?_⟩
    have hd_ne : (d : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    rw [hj]
    push_cast
    rw [show (d : ℤ) * ↑M * j = (d : ℤ) * (M * j) from by ring,
      Int.mul_ediv_cancel_left _ hd_ne]

end HeckeRing.GL2

namespace ModularForm

variable {k : ℤ}

/-- Restrict a modular form along a subgroup inclusion `Γ' ≤ Γ`.

If `f` is `Γ`-invariant, then in particular it's `Γ'`-invariant. Cusps of `Γ'`
are also cusps of `Γ` (by `IsCusp.mono`), so boundedness at cusps transfers. -/
def restrictSubgroup {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ)
    (f : ModularForm Γ k) : ModularForm Γ' k where
  toFun := f.toFun
  slash_action_eq' γ hγ := f.slash_action_eq' γ (h hγ)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

@[simp]
lemma coe_restrictSubgroup {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ)
    (f : ModularForm Γ k) : ⇑(ModularForm.restrictSubgroup h f) = ⇑f := rfl

end ModularForm

namespace CuspForm

variable {k : ℤ}

/-- Restrict a cusp form along a subgroup inclusion `Γ' ≤ Γ`.

If `f` is `Γ`-invariant, then in particular it's `Γ'`-invariant. Cusps of `Γ'` are
also cusps of `Γ` (by `IsCusp.mono`), so cusp-vanishing transfers. -/
def restrictSubgroup {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ)
    (f : CuspForm Γ k) : CuspForm Γ' k where
  toFun := f.toFun
  slash_action_eq' γ hγ := f.slash_action_eq' γ (h hγ)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (hc.mono h)

end CuspForm

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open scoped MatrixGroups ModularForm Pointwise

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The conjugation inclusion `(Γ₁(d*M)).map (mapGL ℝ) ≤ α_d⁻¹ ((Γ₁(M)).map (mapGL ℝ)) α_d`.

This is the key inclusion that lets us restrict the translated cusp form. -/
lemma Gamma1_dmul_le_conj (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] :
    (Gamma1 (d * M)).map (mapGL ℝ) ≤
      ConjAct.toConjAct (levelRaiseMatrix d)⁻¹ • (Gamma1 M).map (mapGL ℝ) := by
  intro g hg
  obtain ⟨γ, hγ_mem, rfl⟩ := Subgroup.mem_map.mp hg
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨mapGL ℝ (levelRaiseConj d M γ hγ_mem),
    Subgroup.mem_map.mpr ⟨_, levelRaiseConj_mem_Gamma1 d M γ hγ_mem, rfl⟩, ?_⟩
  -- Goal: ConjAct.toConjAct (levelRaiseMatrix d)⁻¹ • mapGL ℝ (levelRaiseConj d M γ hγ_mem) =
  --       mapGL ℝ γ
  -- i.e. (levelRaiseMatrix d)⁻¹ * mapGL ℝ (levelRaiseConj ...) * (levelRaiseMatrix d) = mapGL ℝ γ
  -- This is the matrix calculation: δ_d⁻¹ * (δ_d * γ * δ_d⁻¹) * δ_d = γ (which is trivially true)
  -- Or equivalently: levelRaiseMatrix d * mapGL ℝ γ = mapGL ℝ (levelRaiseConj ...) * levelRaiseMatrix d
  rw [ConjAct.toConjAct_smul, inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact levelRaiseMatrix_mul_mapGL d γ (Gamma1_dmul_lower_left_dvd d M γ hγ_mem)

/-- The level-raising operator `ι_d : S_k(Γ₁(M)) → S_k(Γ₁(d*M))`, defined as
`(ι_d f)(τ) = f(d·τ)`, equivalently `d^{1-k} · (f ∣[k] [[d,0],[0,1]])`.

DS (5.16): inclusion `S_k(Γ₁(M)) ↪ S_k(Γ₁(N))` for `M | N`.

**Construction (following Miyake §4.6 Lemma 4.6.1):**
1. Apply `CuspForm.translate f α_d` to get a cusp form for `α_d⁻¹ Γ₁(M) α_d`
2. Restrict via the inclusion `Γ₁(d*M) ≤ α_d⁻¹ Γ₁(M) α_d` (matrix conjugation)
3. Scale by `d^{1-k}` -/
def levelRaise (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ) :
    CuspForm ((Gamma1 M).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 (d * M)).map (mapGL ℝ)) k where
  toFun f :=
    ((d : ℂ) ^ (1 - k)) •
      (CuspForm.translate f (levelRaiseMatrix d)).restrictSubgroup (Gamma1_dmul_le_conj M d)
  map_add' f₁ f₂ := by
    ext z
    show ((d : ℂ) ^ (1 - k)) • ((⇑(f₁ + f₂) ∣[k] levelRaiseMatrix d) z) =
      ((d : ℂ) ^ (1 - k)) • ((⇑f₁ ∣[k] levelRaiseMatrix d) z) +
      ((d : ℂ) ^ (1 - k)) • ((⇑f₂ ∣[k] levelRaiseMatrix d) z)
    simp only [CuspForm.coe_add, SlashAction.add_slash, Pi.add_apply, smul_add]
  map_smul' c f := by
    ext z
    show ((d : ℂ) ^ (1 - k)) • ((⇑(c • f) ∣[k] levelRaiseMatrix d) z) =
      c • (((d : ℂ) ^ (1 - k)) • ((⇑f ∣[k] levelRaiseMatrix d) z))
    have hcoe : (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f := rfl
    have hdet_pos : (0 : ℝ) < (Matrix.GeneralLinearGroup.det (levelRaiseMatrix d) : ℝ) := by
      simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two,
        Nat.cast_pos.mpr (Nat.pos_of_neZero d)]
    have hσ : UpperHalfPlane.σ (levelRaiseMatrix d) = RingHom.id ℂ := by
      unfold UpperHalfPlane.σ
      rw [if_pos hdet_pos]
    simp only [hcoe, ModularForm.smul_slash, hσ, RingHom.id_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- The level-raising operator on `ModularForm`:
`ι_d : M_k(Γ₁(M)) → M_k(Γ₁(d*M))`, sending `f ↦ d^{1-k} · (f ∣[k] α_d)` where
`α_d = [[d, 0], [0, 1]]`.  This is the `ModularForm` analogue of `levelRaise`
(whose target is `CuspForm`); it is the infrastructure blocker identified in
`LeanModularForms/Eigenforms/MainLemma.lean` for bundling `f(dτ)` as a modular
form at the deeper level, needed for Miyake §4.6.5 (coprime sieving).

**Construction** (mirrors `levelRaise`):
1. Apply `ModularForm.translate f α_d` to obtain a modular form for the
   conjugated group `α_d⁻¹ · Γ₁(M) · α_d`.
2. Restrict via `Gamma1_dmul_le_conj` to land in the subgroup `Γ₁(d*M)`.
3. Scale by `d^{1-k}` so that `(ι_d f)(τ) = f(d·τ)` (cf. `levelRaiseFun_apply`).

The pointwise formula `(ι_d f)(τ) = f(d·τ)` is provided by
`modularFormLevelRaise_apply`. -/
def modularFormLevelRaise (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ) :
    ModularForm ((Gamma1 M).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 (d * M)).map (mapGL ℝ)) k where
  toFun f :=
    ((d : ℂ) ^ (1 - k)) •
      (ModularForm.translate f (levelRaiseMatrix d)).restrictSubgroup
        (Gamma1_dmul_le_conj M d)
  map_add' f₁ f₂ := by
    ext z
    show ((d : ℂ) ^ (1 - k)) • ((⇑(f₁ + f₂) ∣[k] levelRaiseMatrix d) z) =
      ((d : ℂ) ^ (1 - k)) • ((⇑f₁ ∣[k] levelRaiseMatrix d) z) +
      ((d : ℂ) ^ (1 - k)) • ((⇑f₂ ∣[k] levelRaiseMatrix d) z)
    simp only [ModularForm.coe_add, SlashAction.add_slash, Pi.add_apply, smul_add]
  map_smul' c f := by
    ext z
    show ((d : ℂ) ^ (1 - k)) • ((⇑(c • f) ∣[k] levelRaiseMatrix d) z) =
      c • (((d : ℂ) ^ (1 - k)) • ((⇑f ∣[k] levelRaiseMatrix d) z))
    have hcoe : (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f := rfl
    have hdet_pos : (0 : ℝ) < (Matrix.GeneralLinearGroup.det (levelRaiseMatrix d) : ℝ) := by
      simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two,
        Nat.cast_pos.mpr (Nat.pos_of_neZero d)]
    have hσ : UpperHalfPlane.σ (levelRaiseMatrix d) = RingHom.id ℂ := by
      unfold UpperHalfPlane.σ
      rw [if_pos hdet_pos]
    simp only [hcoe, ModularForm.smul_slash, hσ, RingHom.id_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- **Coercion of `modularFormLevelRaise` to `UpperHalfPlane → ℂ`.**

`⇑(modularFormLevelRaise M d k f) = d^{1-k} · (⇑f ∣[k] α_d) = levelRaiseFun d k ⇑f`. -/
@[simp]
lemma coe_modularFormLevelRaise (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ⇑(modularFormLevelRaise M d k f) = levelRaiseFun d k ⇑f :=
  rfl

/-! ### Down-conjugation bridge for the slash action

The matrix identity `α_l · γ = γ̃ · α_l` (where `γ̃ = α_l γ α_l⁻¹` constructed
by `levelRaiseConjOfDvd`) lifts to a slash-action equality: applying the
`mapGL ℝ γ`-slash to a level-raised function `levelRaiseFun l k f` is the
same as level-raising the `mapGL ℝ γ̃`-slash of `f`. This packages the
matrix identity (`levelRaiseMatrix_mul_mapGL`) as the level-raise-equivariant
slash bridge needed by Miyake §4.6.4 (Conductor theorem) for transporting
slash conditions across `α_l`. -/

/-- **Down-conjugation bridge.** For `γ : SL(2, ℤ)` with `l ∣ γ.val 1 0` and
`γ̃ := levelRaiseConjOfDvd l γ hdvd = α_l γ α_l⁻¹`, the slash action by
`mapGL ℝ γ` on `levelRaiseFun l k f` equals the level-raise of the slash
action by `mapGL ℝ γ̃` on `f`:

```
(levelRaiseFun l k f) ∣[k] (mapGL ℝ γ) = levelRaiseFun l k (f ∣[k] mapGL ℝ γ̃).
```

This is the slash-action incarnation of `levelRaiseMatrix_mul_mapGL`,
combining `slash_mul`, `smul_slash`, and the determinant-1 fact for `γ ∈
SL(2, ℤ)` (which makes `σ (mapGL ℝ γ)` trivial). -/
lemma slash_mapGL_levelRaiseFun (l : ℕ) [NeZero l] (k : ℤ)
    (γ : SL(2, ℤ)) (hdvd : (l : ℤ) ∣ γ.val 1 0)
    (f : UpperHalfPlane → ℂ) :
    levelRaiseFun l k f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) =
      levelRaiseFun l k
        (f ∣[k] (mapGL ℝ (levelRaiseConjOfDvd l γ hdvd) : GL (Fin 2) ℝ)) := by
  have hσγ : UpperHalfPlane.σ (mapGL ℝ γ : GL (Fin 2) ℝ) = RingHom.id ℂ := by
    unfold UpperHalfPlane.σ
    rw [if_pos]
    show (0 : ℝ) < (Matrix.GeneralLinearGroup.det (mapGL ℝ γ)).val
    rw [Matrix.SpecialLinearGroup.det_mapGL]; norm_num
  show ((l : ℂ) ^ (1 - k) • (f ∣[k] levelRaiseMatrix l)) ∣[k]
      (mapGL ℝ γ : GL (Fin 2) ℝ) = _
  rw [ModularForm.smul_slash, hσγ, RingHom.id_apply, ← SlashAction.slash_mul,
    ← levelRaiseMatrix_mul_mapGL l γ hdvd, SlashAction.slash_mul]
  rfl

/-! ### Pointwise evaluation, surjectivity of `α_l`-action, and injectivity

The `α_l = levelRaiseMatrix l`-action on the upper half plane is the diagonal
scaling `τ ↦ l · τ`, which is surjective with explicit inverse
`τ' ↦ τ' / l`. Combined with the pointwise evaluation
`(levelRaiseFun l k f) τ = f (α_l • τ)`, this yields injectivity of
`levelRaiseFun l k : (ℍ → ℂ) → (ℍ → ℂ)`.

These facts are the missing piece of the Case A direction of
Miyake §4.6.4: they let downstream callers cancel the `levelRaiseFun l k`
wrapper from the level-raised slash identity provided by
`conductor_slash_levelRaise_eq` to obtain the unlifted Nebentypus
relation for the candidate lower-level form `f`. -/

/-- The denominator of `levelRaiseMatrix l` at any point is `1` (bottom row
of `α_l` is `(0, 1)`). -/
lemma denom_levelRaiseMatrix (l : ℕ) [NeZero l] (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (levelRaiseMatrix l) (↑τ : ℂ) = 1 := by
  simp [UpperHalfPlane.denom, levelRaiseMatrix,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- The determinant of `levelRaiseMatrix l` is positive (it equals `l > 0`). -/
lemma levelRaiseMatrix_det_pos (l : ℕ) [NeZero l] :
    (0 : ℝ) < (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l) : ℝ) := by
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.det_fin_two, Nat.cast_pos.mpr (Nat.pos_of_neZero l)]

/-- The real absolute determinant of `levelRaiseMatrix l` is `l`. -/
lemma abs_levelRaiseMatrix_det_val (l : ℕ) [NeZero l] :
    |((Matrix.GeneralLinearGroup.det (levelRaiseMatrix l)) : ℝ)| = (l : ℝ) := by
  rw [abs_of_pos (levelRaiseMatrix_det_pos l)]
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.det_fin_two]

/-- The conjugation factor `σ` for `levelRaiseMatrix l` is the identity
(positive determinant). -/
lemma σ_levelRaiseMatrix (l : ℕ) [NeZero l] :
    UpperHalfPlane.σ (levelRaiseMatrix l) = RingHom.id ℂ := by
  unfold UpperHalfPlane.σ
  rw [if_pos (levelRaiseMatrix_det_pos l)]

/-- **Pointwise evaluation of the level-raise operator.**
`levelRaiseFun l k f` evaluates to `f` at the scaled point `α_l • τ`:

```
(levelRaiseFun l k f) τ = f (levelRaiseMatrix l • τ).
```

The `l^{1-k}` scalar prefactor in the definition of `levelRaiseFun` exactly
cancels the `l^{k-1}` factor from the slash action, yielding the un-rescaled
evaluation `f (α_l • τ)`. -/
lemma levelRaiseFun_apply (l : ℕ) [NeZero l] (k : ℤ) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    levelRaiseFun l k f τ = f ((levelRaiseMatrix l) • τ) := by
  show ((l : ℂ) ^ (1 - k)) • ((f ∣[k] levelRaiseMatrix l) τ) = _
  rw [ModularForm.slash_apply, σ_levelRaiseMatrix, RingHom.id_apply,
    abs_levelRaiseMatrix_det_val, denom_levelRaiseMatrix, one_zpow, mul_one]
  have hl_ne : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
  rw [show ((l : ℝ) ^ (k - 1) : ℂ) = (l : ℂ) ^ (k - 1) from by
    push_cast; rfl, smul_eq_mul,
    show (l : ℂ) ^ (1 - k) * (f (levelRaiseMatrix l • τ) * (l : ℂ) ^ (k - 1)) =
        ((l : ℂ) ^ (1 - k) * (l : ℂ) ^ (k - 1)) * f (levelRaiseMatrix l • τ) from by ring,
    ← zpow_add₀ hl_ne, show (1 - k) + (k - 1) = 0 from by ring, zpow_zero, one_mul]

/-- The action of `levelRaiseMatrix l = [[l, 0], [0, 1]]` on `ℍ` is the diagonal
scaling: `(α_l • τ : ℂ) = l · (↑τ : ℂ)`. Direct unfolding of the GL action via
`coe_smul_of_det_pos` together with `num α_l τ = l · τ` and `denom α_l τ = 1`. -/
lemma coe_levelRaiseMatrix_smul (l : ℕ) [NeZero l] (τ : UpperHalfPlane) :
    ((levelRaiseMatrix l • τ : UpperHalfPlane) : ℂ) = (l : ℂ) * (↑τ : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (levelRaiseMatrix_det_pos l)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, levelRaiseMatrix,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- **Pointwise evaluation** of the `ModularForm` level-raising operator:
`(modularFormLevelRaise M d k f) τ = f (α_d • τ)`, where `α_d` acts as
`τ ↦ d · τ` on `ℍ`.  Derived from `levelRaiseFun_apply` via
`coe_modularFormLevelRaise`. -/
lemma modularFormLevelRaise_apply (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (τ : UpperHalfPlane) :
    modularFormLevelRaise M d k f τ = f ((levelRaiseMatrix d) • τ) := by
  rw [show (modularFormLevelRaise M d k f) τ = levelRaiseFun d k (⇑f) τ from rfl]
  exact levelRaiseFun_apply d k (⇑f) τ

/-- **Scaled pointwise formula** for the `ModularForm` level-raising operator:
the level-raised form at `τ` equals `f` at the complex number `d · τ` (viewed
as an upper-half-plane point).  Follows from `modularFormLevelRaise_apply` and
`coe_levelRaiseMatrix_smul`. -/
lemma modularFormLevelRaise_apply_mul (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (τ : UpperHalfPlane) :
    (modularFormLevelRaise M d k f τ : ℂ) =
      f (UpperHalfPlane.mk ((d : ℂ) * (↑τ : ℂ)) (by
        rw [show ((d : ℂ) : ℂ) = ((d : ℝ) : ℂ) from by push_cast; rfl,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        exact mul_pos (Nat.cast_pos.mpr (Nat.pos_of_neZero d)) τ.im_pos)) := by
  rw [modularFormLevelRaise_apply]
  congr 1
  apply UpperHalfPlane.ext
  rw [coe_levelRaiseMatrix_smul]

/-- **Surjectivity of `α_l • _` on `ℍ`.** For every `τ' : ℍ` there exists
`τ : ℍ` with `levelRaiseMatrix l • τ = τ'`; the explicit witness is
`τ = UpperHalfPlane.mk (↑τ' / l)` (with positive imaginary part since
`τ'.im > 0` and `l > 0`). -/
lemma exists_levelRaiseMatrix_smul_eq (l : ℕ) [NeZero l] (τ' : UpperHalfPlane) :
    ∃ τ : UpperHalfPlane, levelRaiseMatrix l • τ = τ' := by
  have hl_ne : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
  have hl_pos : (0 : ℝ) < (l : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero l)
  have him : 0 < ((↑τ' / (l : ℂ) : ℂ)).im := by
    rw [show ((l : ℂ) : ℂ) = ((l : ℝ) : ℂ) from by push_cast; rfl,
      Complex.div_ofReal_im]
    exact div_pos τ'.im_pos hl_pos
  refine ⟨UpperHalfPlane.mk (↑τ' / (l : ℂ)) him, ?_⟩
  apply UpperHalfPlane.ext
  rw [coe_levelRaiseMatrix_smul, UpperHalfPlane.coe_mk]
  field_simp

/-- **Injectivity of `levelRaiseFun l k`.** If two functions `f₁, f₂ : ℍ → ℂ`
have the same level-raise, they are equal. Combines `levelRaiseFun_apply`
(level-raising is precomposition with `α_l • _`) with
`exists_levelRaiseMatrix_smul_eq` (the surjectivity of `α_l • _`). -/
lemma levelRaiseFun_injective (l : ℕ) [NeZero l] (k : ℤ) :
    Function.Injective (levelRaiseFun (k := k) l) := by
  intro f₁ f₂ heq
  funext τ'
  obtain ⟨τ, hτ⟩ := exists_levelRaiseMatrix_smul_eq l τ'
  have h := congr_fun heq τ
  rw [levelRaiseFun_apply, levelRaiseFun_apply, hτ] at h
  exact h

/-! ### Lower-level T-factorisation for slash invariance (T046)

The slash bridge `conductor_slash_T_conj_eq` from T044 gives the slash
identity for matrices of the form `T^i · γ̃ · T^j` where γ̃ is in the
α_l-conjugation image. To extend the slash identity to ALL of `Γ₀(N/l)`,
we need a group-theoretic factorisation: every `γ' ∈ Γ₀(N/l)` decomposes
as `T^i · γ̃ · T^j` for some integers `i, j` and γ̃ in the image.

The math: for `γ' = [[a, b], [c, d]] ∈ Γ₀(N/l)`,

* Choose `i ∈ ℤ` so that `gcd(a - i·c, l) = 1`. Such `i` exists because
  `gcd(a, c) = 1` (from `det γ' = 1`); concretely, take `i` to be the
  product of primes `p ∣ l` with `p ∤ a`. — `exists_shift_isCoprime`.
* Choose `j ∈ ℤ` so that `l ∣ (b - i·d) - j·(a - i·c)`. Solvable because
  `(a - i·c)` is invertible mod `l` (from the previous step) via Bezout.
  — `shiftJ_spec`.
* Then `T^(-i) · γ' · T^(-j)` has upper-right entry divisible by `l`,
  hence equals `levelRaiseConjOfDvd l γ` for an explicit
  `γ ∈ Γ₀(N)` — the actual matrix construction and the equality
  `γ' = T^i · (levelRaiseConjOfDvd l γ) · T^j` is the remaining
  composition step (next ticket).

The two private helper lemmas (`exists_shift_isCoprime` and
`shiftJ_spec`) provide the non-trivial existence/CRT content; the
final assembly into `exists_T_levelRaiseConj_T_factor` is the
mechanical matrix arithmetic — both layers are landed sorry-free in
this file. -/

/-- Auxiliary integer: the product of primes `p` dividing `l` but not
dividing `a`. Casting `Nat → ℤ` for use in the SL(2, ℤ) matrix
calculations. -/
private noncomputable def primeProductCoprime (a : ℤ) (l : ℕ) : ℤ :=
  ((l.primeFactors.filter (fun (p : ℕ) => ¬ ((p : ℤ) ∣ a))).prod id : ℕ)

/-- For a prime `p` dividing `l` but not `a`, `p` divides the auxiliary
shift integer `primeProductCoprime a l`. -/
private lemma dvd_primeProductCoprime_of_not_dvd
    {a : ℤ} {l : ℕ} {p : ℕ} (hp : p ∈ l.primeFactors) (hpa : ¬ ((p : ℤ) ∣ a)) :
    (p : ℤ) ∣ primeProductCoprime a l := by
  unfold primeProductCoprime
  have h_mem : p ∈ l.primeFactors.filter (fun (q : ℕ) => ¬ ((q : ℤ) ∣ a)) := by
    rw [Finset.mem_filter]; exact ⟨hp, hpa⟩
  have hp_dvd_prod : p ∣ (l.primeFactors.filter (fun (q : ℕ) => ¬ ((q : ℤ) ∣ a))).prod id :=
    Finset.dvd_prod_of_mem _ h_mem
  exact_mod_cast hp_dvd_prod

/-- For a prime `p` dividing `l` AND dividing `a`, `p` does NOT divide
the auxiliary shift integer `primeProductCoprime a l`: by construction
it is a product of primes excluded by the filter. -/
private lemma not_dvd_primeProductCoprime_of_dvd
    {a : ℤ} {l : ℕ} {p : ℕ} (hp_prime : p.Prime) (hpa : (p : ℤ) ∣ a) :
    ¬ ((p : ℤ) ∣ primeProductCoprime a l) := by
  unfold primeProductCoprime
  intro h_dvd
  have h_dvd_nat : p ∣ (l.primeFactors.filter (fun (q : ℕ) => ¬ ((q : ℤ) ∣ a))).prod id := by
    exact_mod_cast h_dvd
  have hp_prime' : Prime p := Nat.prime_iff.mp hp_prime
  obtain ⟨q, hq_mem, hq_dvd⟩ :=
    (Prime.dvd_finset_prod_iff hp_prime' id).mp h_dvd_nat
  rw [Finset.mem_filter] at hq_mem
  obtain ⟨hq_pf, hqa⟩ := hq_mem
  -- hq_dvd : p ∣ id q = q. p prime divides prime q ⟹ p = q.
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_pf
  have h_eq : p = q := by
    show id p = id q
    exact (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hq_dvd
  exact hqa (h_eq ▸ hpa)

/-- **Coprime shift existence.** Given `a, c : ℤ` with `IsCoprime a c` and
`l : ℕ` with `l ≠ 0`, there exists `i : ℤ` (concretely
`primeProductCoprime a l`) such that `IsCoprime (a - i*c) (l : ℤ)`. -/
private lemma exists_shift_isCoprime (a c : ℤ) (l : ℕ) [NeZero l]
    (hac : IsCoprime a c) :
    IsCoprime (a - primeProductCoprime a l * c) (l : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd, Int.natAbs_natCast]
  -- Goal: (a - i*c).natAbs.gcd l = 1
  by_contra h_ne_one
  -- pick a prime divisor p of the gcd
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd h_ne_one
  rw [Nat.dvd_gcd_iff] at hp_dvd
  obtain ⟨hp_dvd_x, hp_dvd_l⟩ := hp_dvd
  -- p divides x = (a - i*c).natAbs and p divides l
  have hp_in_pf : p ∈ l.primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hp_prime, hp_dvd_l, NeZero.ne l⟩
  have hp_dvd_x_int : (p : ℤ) ∣ (a - primeProductCoprime a l * c) := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
    exact hp_dvd_x
  have hp_isPrime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
  by_cases hpa : (p : ℤ) ∣ a
  · -- Case: p ∣ a. Then p ∤ i (by construction), p ∤ c (gcd(a,c) = 1),
    -- so p ∤ i*c, hence (a - i*c) ≡ -i*c ≢ 0 (mod p). Contradiction.
    have hp_not_dvd_i : ¬ ((p : ℤ) ∣ primeProductCoprime a l) :=
      not_dvd_primeProductCoprime_of_dvd hp_prime hpa
    have hp_not_dvd_c : ¬ ((p : ℤ) ∣ c) := by
      intro hpc
      exact hp_isPrime.not_unit (hac.isUnit_of_dvd' hpa hpc)
    -- a ≡ 0, so a - i*c ≡ -i*c (mod p). p ∣ (a - i*c) and p ∣ a give p ∣ i*c.
    have hp_dvd_ic : (p : ℤ) ∣ primeProductCoprime a l * c := by
      have h1 : (p : ℤ) ∣ (a - (a - primeProductCoprime a l * c)) :=
        dvd_sub hpa hp_dvd_x_int
      simpa using h1
    rcases hp_isPrime.dvd_mul.mp hp_dvd_ic with h | h
    · exact hp_not_dvd_i h
    · exact hp_not_dvd_c h
  · -- Case: p ∤ a. Then p ∣ i, so p ∣ i*c, so a - i*c ≡ a (mod p), and p ∤ a.
    have hp_dvd_i : (p : ℤ) ∣ primeProductCoprime a l :=
      dvd_primeProductCoprime_of_not_dvd hp_in_pf hpa
    have hp_dvd_ic : (p : ℤ) ∣ primeProductCoprime a l * c :=
      Dvd.dvd.mul_right hp_dvd_i _
    -- a - i*c ≡ a (mod p), but p ∤ a. p ∣ (a - i*c) and p ∣ i*c ⟹ p ∣ a.
    have hp_dvd_a : (p : ℤ) ∣ a := by
      have h1 : (p : ℤ) ∣ ((a - primeProductCoprime a l * c) +
        primeProductCoprime a l * c) := dvd_add hp_dvd_x_int hp_dvd_ic
      simpa using h1
    exact hpa hp_dvd_a

/-- Auxiliary integer for the second shift: given the coprime shift result
`gcd(α, l) = 1`, this returns an integer `j := Bezout coeff · β` such that
`l ∣ (β - j · α)`. Built from `Int.gcdA` (the Bezout coefficient). -/
private noncomputable def shiftJ (α β : ℤ) (l : ℤ) : ℤ :=
  Int.gcdA α l * β

/-- Specification of `shiftJ`: when `Int.gcd α l = 1`, the integer
`j := shiftJ α β l` satisfies `l ∣ (β - j · α)`. Direct consequence of
Bezout: `α · gcdA + l · gcdB = 1` ⟹ `gcdA · α ≡ 1 (mod l)` ⟹
`gcdA · β · α ≡ β (mod l)`. -/
private lemma shiftJ_spec {α β : ℤ} {l : ℕ} (h : Int.gcd α (l : ℤ) = 1) :
    (l : ℤ) ∣ (β - shiftJ α β (l : ℤ) * α) := by
  unfold shiftJ
  -- Bezout: gcd α l = α * Int.gcdA α l + l * Int.gcdB α l
  have hBezout := Int.gcd_eq_gcd_ab α (l : ℤ)
  rw [show ((Int.gcd α (l : ℤ) : ℕ) : ℤ) = 1 from by exact_mod_cast h] at hBezout
  -- hBezout : 1 = α * Int.gcdA α (l : ℤ) + ↑l * Int.gcdB α (l : ℤ)
  -- Want: l ∣ β - (Int.gcdA α l * β) * α = β - β * (α * Int.gcdA α l) = β * (1 - α * Int.gcdA α l)
  --     = β * (l * Int.gcdB α l)  (from Bezout: α*gcdA = 1 - l*gcdB)
  refine ⟨β * Int.gcdB α (l : ℤ), ?_⟩
  linear_combination β * hBezout

/-- Helper: if `l ∣ N` and `γ ∈ Γ₀(N)`, then `(l : ℤ) ∣ γ.val 1 0`. -/
private lemma dvd_lower_left_of_dvd
    {l N : ℕ} (h_dvd : l ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    (l : ℤ) ∣ γ.val 1 0 := by
  rw [Gamma0_mem] at hγ
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h_dvd) h

/-- **Lower-level T-factorisation.** Every `γ' ∈ Γ₀(N/l)` can be written as
`T^i · (levelRaiseConjOfDvd l γ ...) · T^j` for explicit integers `i, j`
and an explicit `γ ∈ Γ₀(N)`.

This is the central group-theoretic input for extending the slash bridge
`conductor_slash_T_conj_eq` from T044 to the full lower level `Γ₀(N/l)`.

**Construction.** For `γ' = [[a, b], [c, d]] ∈ Γ₀(N/l)`:
* `i := primeProductCoprime a l` (CRT shift, makes `gcd(a - i·c, l) = 1`).
* `j := shiftJ (a - i·c) (b - i·d) (l : ℤ)` (Bezout shift, makes
  `l ∣ (b - i·d) - j·(a - i·c)`).
* The lifted `γ ∈ Γ₀(N)` is `[[a - i·c, k; l·c, d - c·j]]` where
  `k = ((b - i·d) - j·(a - i·c))/l`.

The product `T^i · γ̃ · T^j` (with `γ̃ = α_l γ α_l⁻¹`) recovers `γ'`
by direct matrix calculation. -/
lemma exists_T_levelRaiseConj_T_factor
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N)
    (γ' : SL(2, ℤ)) (hγ' : γ' ∈ Gamma0 (N / l)) :
    ∃ (i j : ℤ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N),
      γ' = ModularGroup.T ^ i *
            (levelRaiseConjOfDvd l γ (dvd_lower_left_of_dvd h_dvd hγ)) *
            ModularGroup.T ^ j ∧
      γ.val 1 1 = γ'.val 1 1 - γ'.val 1 0 * j := by
  -- Step 1: extract entries of γ'.
  set a := γ'.val 0 0 with ha_def
  set b := γ'.val 0 1 with hb_def
  set c := γ'.val 1 0 with hc_def
  set d := γ'.val 1 1 with hd_def
  -- Step 2: derive IsCoprime a c from det = 1.
  have hdet : a * d - b * c = 1 := by
    have hp := γ'.property
    rw [Matrix.det_fin_two] at hp
    simpa [a, b, c, d] using hp
  have hac : IsCoprime a c := ⟨d, -b, by linear_combination hdet⟩
  -- Step 3: apply exists_shift_isCoprime.
  set i := primeProductCoprime a l with hi_def
  set α := a - i * c with hα_def
  have hα_iscop : IsCoprime α (l : ℤ) := exists_shift_isCoprime a c l hac
  have hα_gcd : Int.gcd α (l : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hα_iscop
  -- Step 4: apply shiftJ_spec to obtain k. Specify β explicitly.
  set β := b - i * d with hβ_def
  set j := shiftJ α β (l : ℤ) with hj_def
  obtain ⟨k, hk⟩ := shiftJ_spec (β := β) hα_gcd
  -- hk : β - j * α = (l : ℤ) * k, equivalently β - j * α = l * k
  -- Step 5: construct γ and verify det = 1.
  refine ⟨i, j, ⟨!![α, k; (l : ℤ) * c, d - c * j], ?det⟩,
    ?gamma0_mem, ?eq, ?diag⟩
  · -- det = 1
    rw [Matrix.det_fin_two_of]
    -- Goal: α * (d - c * j) - k * ((l : ℤ) * c) = 1
    -- Use: hdet (a*d - b*c = 1), hk (β - j*α = l*k), unfolds α = a - i*c, β = b - i*d.
    show α * (d - c * j) - k * ((l : ℤ) * c) = 1
    have : α = a - i * c := hα_def
    have : β = b - i * d := hβ_def
    linear_combination hdet + c * hk
  · -- γ ∈ Gamma0 N: lower-left entry l*c is divisible by N = l * (N/l).
    rw [Gamma0_mem]
    show (((l : ℤ) * c : ℤ) : ZMod N) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    -- Have hγ' : γ' ∈ Gamma0 (N/l), so (N/l) ∣ c.
    rw [Gamma0_mem] at hγ'
    have hc_dvd : ((N / l : ℕ) : ℤ) ∣ c :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ'
    obtain ⟨m, hm⟩ := hc_dvd
    refine ⟨m, ?_⟩
    rw [hm]
    have hN : N = l * (N / l) := (Nat.mul_div_cancel' h_dvd).symm
    rw [show ((N : ℤ) : ℤ) = ((l * (N / l) : ℕ) : ℤ) from by rw [← hN]]
    push_cast
    ring
  · -- Product equality: γ' = T^i · (levelRaiseConjOfDvd l γ ...) · T^j
    apply Subtype.ext
    have hl_ne : (l : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
    have h_div : ((l : ℤ) * c) / (l : ℤ) = c := Int.mul_ediv_cancel_left c hl_ne
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ModularGroup.coe_T_zpow, ModularGroup.coe_T_zpow]
    apply Matrix.ext
    intro p q
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    have ha : γ'.val 0 0 = a := rfl
    have hb : γ'.val 0 1 = b := rfl
    have hc : γ'.val 1 0 = c := rfl
    have hd : γ'.val 1 1 = d := rfl
    fin_cases p <;> fin_cases q <;>
      simp [levelRaiseConjOfDvd, h_div, hα_def, hβ_def, hj_def, ha, hb, hc, hd]
    -- After simp, four entry-equality goals remain; (0,1) needs hk.
    · linear_combination hk
    -- (Other three goals close with `ring` reflex via simp's normalisation;
    --  if any remain, follow up with linear_combination.)
  · -- Diagonal entry: γ.val 1 1 = d - c*j = γ'.val 1 1 - γ'.val 1 0 * j.
    rfl

/-! ### q-expansion scaling formula for `modularFormLevelRaise` (T068)

The bundled level-raise `modularFormLevelRaise N d k f` sends `f` to the
modular form whose underlying function is `τ ↦ f (d · τ)`.  Its Fourier
coefficients at the base period `(N : ℝ)` are obtained by **d-dilation
with zeros at non-multiples of `d`**: the coefficient at `n` is
`(qExpansion N f).coeff (n / d)` if `d ∣ n`, and `0` otherwise.

**Scope note for Miyake §4.6.5 (coprime sieving).**  T068 provides the
d-dilation coefficient formula *only*.  The plain Möbius-weighted sum
`Σ_{d ∣ L} μ(d) · modularFormLevelRaise N d k f` has `n`-th coefficient
`Σ_{d ∣ gcd(n, L)} μ(d) · (qExpansion N f).coeff (n / d)`, which in
general does **not** equal the sieved coefficient
`(qExpansion N f).coeff n · [gcd(n, L) = 1]`: the Möbius indicator
identity `coprime_indicator_eq_sum_moebius` applies only to a fixed
scalar coefficient, whereas here the coefficient `a_{n/d}` depends on
`d`.  Miyake's Theorem 4.6.5 collapses the two via additional
eigenform/normalization hypotheses (Hecke eigenvalue relations linking
`a_{n/d}` to `a_n`) that are **not** encoded by T068 alone.  Deriving
`sievedQExpansion` from the level-raise sum therefore requires further
infrastructure; T068 is the first ingredient, not the full assembly.

## Pure-hasSum / qParam helpers

These two helpers are standalone power-series / complex-exponential
facts with no dependency on the level-raising infrastructure; they are
kept private to avoid namespace pollution.  Analogous lemmas exist in
`Eigenforms.HeckeLemma` (`qParam_mul_nat`, `hasSum_pow_mul_reindex`),
duplicated here to keep `LevelRaise.lean`'s import footprint minimal. -/

/-- **qParam scaling under `d`-dilation.**  For positive `N : ℝ` and
positive integer `d`, `qParam N (d · z) = (qParam N z) ^ d`.

This is the pure-exponential identity behind the q-expansion dilation:
substituting `d · τ` in place of `τ` inside the q-parameter raises it to
the `d`-th power. -/
lemma qParam_nat_mul_eq_pow (h : ℝ) (d : ℕ) (z : ℂ) :
    Function.Periodic.qParam h ((d : ℂ) * z) =
      (Function.Periodic.qParam h z) ^ d := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- **Sparse reindexing** of a HasSum over `(q^d)^j` as a HasSum over
`q^n` with zero coefficients at non-multiples of `d`.  For
`HasSum (j ↦ a j • (q ^ d) ^ j) S`, we obtain
`HasSum (n ↦ if d ∣ n then a (n / d) • q ^ n else 0) S`. -/
lemma hasSum_pow_dvd_reindex {d : ℕ} (hd : 0 < d) {a : ℕ → ℂ} {q : ℂ}
    {S : ℂ} (h : HasSum (fun j : ℕ => a j • (q ^ d) ^ j) S) :
    HasSum (fun n : ℕ => if d ∣ n then a (n / d) • q ^ n else 0) S := by
  have hinj : Function.Injective (fun j : ℕ => d * j) := fun _ _ hxy =>
    Nat.mul_left_cancel hd hxy
  have h_zero : ∀ n : ℕ, n ∉ Set.range (fun j : ℕ => d * j) →
      (fun n : ℕ => if d ∣ n then a (n / d) • q ^ n else 0) n = 0 := by
    intro n hn
    simp only
    rw [if_neg]
    intro hdvd
    obtain ⟨j, rfl⟩ := hdvd
    exact hn ⟨j, rfl⟩
  have h_eq : ((fun n : ℕ => if d ∣ n then a (n / d) • q ^ n else 0) ∘
      (fun j : ℕ => d * j)) = fun j : ℕ => a j • (q ^ d) ^ j := by
    funext j
    simp only [Function.comp_apply]
    rw [if_pos ⟨j, rfl⟩]
    congr 1
    · exact congrArg a (Nat.mul_div_cancel_left j hd)
    · rw [← pow_mul]
  rw [← Function.Injective.hasSum_iff hinj h_zero, h_eq]
  exact h

/-- **q-expansion scaling formula for `modularFormLevelRaise`** (T068).

For `f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k` and positive integer
`d`, the level-raised form `modularFormLevelRaise N d k f` has
`(N : ℝ)`-level Fourier coefficients:

```
(qExpansion (N : ℝ) (modularFormLevelRaise N d k f)).coeff n =
  if d ∣ n then (qExpansion (N : ℝ) f).coeff (n / d) else 0.
```

**Scaling factor cancellation.**  By
`slash_diagGL_Q_lower_apply`/pointwise, `(f ∣[k] α_d)(τ) = d^{k-1} ·
f(d·τ)`, and `modularFormLevelRaise` multiplies by `d^{1-k}`; the factors
cancel exactly, so the level-raised form is `τ ↦ f(d·τ)` with **no
residual scalar**.  The coefficient formula is therefore pure d-dilation
(no `d^{k-1}` prefactor), which is what `coprime_indicator_eq_sum_moebius`
and the Möbius sieving assembly consume.

**Proof outline.**
1. Pointwise `(modularFormLevelRaise N d k f) τ = f (α_d • τ) = f(d·τ)`
   via `modularFormLevelRaise_apply`.
2. `hasSum_qExpansion f` evaluated at `α_d • τ` gives
   `HasSum (n ↦ (qExpansion N f).coeff n • qParam N ((α_d • τ) : ℂ) ^ n)
     (f (α_d • τ))`.
3. `coe_levelRaiseMatrix_smul` + `qParam_nat_mul_eq_pow` rewrite
   `qParam N ((α_d • τ) : ℂ) = qParam N τ ^ d`.
4. `hasSum_pow_dvd_reindex` reindexes sparsely `(q^d)^n ↦ q^j` with
   zero coefficients at non-multiples of `d`.
5. `qExpansion_coeff_unique` reads off the coefficient at index `n`. -/
theorem qExpansion_modularFormLevelRaise_coeff
    {N : ℕ} [NeZero N] {d : ℕ} [NeZero d] {k : ℤ}
    (hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion (N : ℝ) (modularFormLevelRaise N d k f)).coeff n =
      if d ∣ n then (qExpansion (N : ℝ) f).coeff (n / d) else 0 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
  have hd_pos : 0 < d := Nat.pos_of_neZero d
  have hN_period_dN :
      (N : ℝ) ∈ ((Gamma1 (d * N)).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 (d * N)).map (mapGL ℝ) =
      (Gamma1 (d * N) : Subgroup (GL (Fin 2) ℝ)) from rfl, strictPeriods_Gamma1]
    exact ⟨(N : ℤ), by simp⟩
  -- Build a HasSum for `(modularFormLevelRaise N d k f) τ` at period `N`
  -- with sparse d-dilated coefficients.
  have h_sum_g : ∀ τ : UpperHalfPlane,
      HasSum (fun j : ℕ =>
        (if d ∣ j then (qExpansion (N : ℝ) f).coeff (j / d) else 0) •
          Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ j)
        (modularFormLevelRaise N d k f τ) := by
    intro τ
    -- Pointwise: (modularFormLevelRaise N d k f) τ = f (α_d • τ).
    rw [modularFormLevelRaise_apply N d k f τ]
    -- f's q-expansion HasSum at the scaled point.
    have hfsum := hasSum_qExpansion f hN_pos hN_period (levelRaiseMatrix d • τ)
    -- qParam N ((α_d • τ) : ℂ) = qParam N τ ^ d.
    have hqeq :
        Function.Periodic.qParam (N : ℝ) ((levelRaiseMatrix d • τ :
          UpperHalfPlane) : ℂ) =
          (Function.Periodic.qParam (N : ℝ) (τ : ℂ)) ^ d := by
      rw [coe_levelRaiseMatrix_smul d τ]
      exact qParam_nat_mul_eq_pow (N : ℝ) d (τ : ℂ)
    rw [hqeq] at hfsum
    -- Reindex sparsely via hasSum_pow_dvd_reindex, and move the `if`
    -- inside the `•` via `ite_smul`.
    have hreidx := hasSum_pow_dvd_reindex hd_pos hfsum
    convert hreidx using 1
    funext j
    split_ifs with hdvd
    · rfl
    · simp
  -- Apply qExpansion_coeff_unique to read off the coefficient.
  exact (qExpansion_coeff_unique hN_pos hN_period_dN h_sum_g n).symm

/-- **Period-general q-expansion scaling formula for `modularFormLevelRaise`.**

Generalises `qExpansion_modularFormLevelRaise_coeff` to an arbitrary
positive period `h` that is a strict period of **both** `Γ₁(N)` (the
source level of `f`) and `Γ₁(d · N)` (the target level of `ι_d f`).
Since every integer is a strict period of every `Γ₁(M)`, the natural
applications are at period `h = 1` (canonical Fourier period) or at any
integer divisor of the coarser level.

The proof is structurally identical to
`qExpansion_modularFormLevelRaise_coeff` with `h` substituted for
`(N : ℝ)` throughout. -/
theorem qExpansion_modularFormLevelRaise_coeff'
    {N : ℕ} [NeZero N] {d : ℕ} [NeZero d] {k : ℤ} {h : ℝ}
    (hh_pos : 0 < h)
    (hh_period_N : h ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    (hh_period_dN : h ∈ ((Gamma1 (d * N)).map (mapGL ℝ)).strictPeriods)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion h (modularFormLevelRaise N d k f)).coeff n =
      if d ∣ n then (qExpansion h f).coeff (n / d) else 0 := by
  have hd_pos : 0 < d := Nat.pos_of_neZero d
  have h_sum_g : ∀ τ : UpperHalfPlane,
      HasSum (fun j : ℕ =>
        (if d ∣ j then (qExpansion h f).coeff (j / d) else 0) •
          Function.Periodic.qParam h (τ : ℂ) ^ j)
        (modularFormLevelRaise N d k f τ) := by
    intro τ
    rw [modularFormLevelRaise_apply N d k f τ]
    have hfsum := hasSum_qExpansion f hh_pos hh_period_N (levelRaiseMatrix d • τ)
    have hqeq :
        Function.Periodic.qParam h ((levelRaiseMatrix d • τ :
          UpperHalfPlane) : ℂ) =
          (Function.Periodic.qParam h (τ : ℂ)) ^ d := by
      rw [coe_levelRaiseMatrix_smul d τ]
      exact qParam_nat_mul_eq_pow h d (τ : ℂ)
    rw [hqeq] at hfsum
    have hreidx := hasSum_pow_dvd_reindex hd_pos hfsum
    convert hreidx using 1
    funext j
    split_ifs with hdvd
    · rfl
    · simp
  exact (qExpansion_coeff_unique hh_pos hh_period_dN h_sum_g n).symm

/-- **Period-1 specialisation** of `qExpansion_modularFormLevelRaise_coeff'`:
for any `f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k`, the canonical
Fourier expansion of `modularFormLevelRaise N d k f` satisfies

`(qExpansion 1 (modularFormLevelRaise N d k f)).coeff n =
  if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0`.

This is the version suitable for consumption by Miyake-style single-prime
sieve arguments (T070/T073 period-1 variants in `MainLemma.lean`), where
the witness no-diamond hypothesis is naturally stated at period 1. -/
theorem qExpansion_one_modularFormLevelRaise_coeff
    {N : ℕ} [NeZero N] {d : ℕ} [NeZero d] {k : ℤ}
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion (1 : ℝ) (modularFormLevelRaise N d k f)).coeff n =
      if d ∣ n then (qExpansion (1 : ℝ) f).coeff (n / d) else 0 := by
  have h1_period_N :
      (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) =
      (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl, strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  have h1_period_dN :
      (1 : ℝ) ∈ ((Gamma1 (d * N)).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 (d * N)).map (mapGL ℝ) =
      (Gamma1 (d * N) : Subgroup (GL (Fin 2) ℝ)) from rfl, strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  exact qExpansion_modularFormLevelRaise_coeff' one_pos h1_period_N h1_period_dN f n

end HeckeRing.GL2


end
