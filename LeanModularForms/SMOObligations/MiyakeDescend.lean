/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.SMOObligations.DescentCosets

/-!
# Strong Multiplicity One via Miyake §4.6 — Hecke descent map

The `multipass_*` slash-sum machinery and the Hecke descent linear map
`miyake_hecke_descend` together with its q-expansion/character properties.
Part of a multi-file split of `SMOObligations.lean`.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- For `g : GL (Fin 2) ℝ` with positive determinant, `UpperHalfPlane.σ g` is the identity. -/
lemma multipass_sigma_eq_id_of_det_pos (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) : UpperHalfPlane.σ g = RingHom.id ℂ := by
  simp only [UpperHalfPlane.σ, if_pos hg]

/-- For `γ ∈ Γ₁(N)`, there exists `hγ' : γ ∈ Γ₀(N)` with `Gamma0MapUnits ⟨γ, hγ'⟩ = 1`. -/
lemma multipass_char_trivial_on_Gamma1 {N : ℕ} [NeZero N]
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ Gamma1 N) :
    ∃ hγ' : γ ∈ Gamma0 N,
      Gamma0MapUnits (N := N) ⟨γ, hγ'⟩ = 1 := by
  rw [Gamma1_mem] at hγ
  obtain ⟨_h00, h11, h10⟩ := hγ
  exact ⟨Gamma0_mem.mpr h10, by ext; simpa [Gamma0MapUnits_val, Gamma0Map] using h11⟩

/-- For `f ∈ modFormCharSpace k χ` and `α ∈ Γ₀(N)`, `f ∣[k] mapGL ℝ α = χ(α) • f`. -/
lemma multipass_modFormCharSpace_slash_apply
    {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hfχ : f ∈ modFormCharSpace k χ)
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hα : α ∈ Gamma0 N) :
    (⇑f ∣[k] (mapGL ℝ α : GL (Fin 2) ℝ) : UpperHalfPlane → ℂ) =
      ((χ (Gamma0MapUnits ⟨α, hα⟩) : ℂ) • ⇑f) :=
  (modFormCharSpace_iff_nebentypus k χ f).mp hfχ ⟨α, hα⟩

/-- If the image of `α ∈ SL(2, ℤ)` under reduction mod `N` equals the identity, then
`α ∈ Γ_1(N)`. -/
lemma multipass_gamma1_conjugate_in_gamma1
    {N : ℕ} [NeZero N]
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h_α_mod_N : ((α : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) = 1)) :
    α ∈ Gamma1 N := by
  rw [Gamma1_mem]
  have h : ∀ i j : Fin 2, Int.cast (α i j) = (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) i j :=
    fun i j ↦ congr_fun (congr_fun h_α_mod_N i) j ▸ by simp [Matrix.map_apply]
  simp only [Matrix.one_apply] at h
  exact ⟨h 0 0, h 1 1, h 1 0⟩

/-- When `l` is coprime to prime `p`, there exists a permutation `σ` of `Fin p`
satisfying `(σ m).val = (l * m.val) % p` for all `m`. -/
lemma multipass_mul_mod_p_perm_exists {p l : ℕ} [NeZero p] (hp : p.Prime) (hpl : Nat.Coprime p l) :
    ∃ σ : Equiv.Perm (Fin p), ∀ m : Fin p, (σ m).val = (l * m.val) % p := by
  have : Fact p.Prime := ⟨hp⟩
  let f : Fin p → Fin p := fun m ↦ ⟨(l * m.val) % p, Nat.mod_lt _ hp.pos⟩
  have hl_ne : (l : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hp.coprime_iff_not_dvd.mp hpl
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hab_val : (l * a.val) % p = (l * b.val) % p := congr_arg Fin.val hab
    have h_zmod : ((l : ZMod p) * (a.val : ZMod p)) = ((l : ZMod p) * (b.val : ZMod p)) := by
      simpa [ZMod.natCast_mod] using congr_arg (Nat.cast : ℕ → ZMod p) hab_val
    exact Fin.val_injective (by rw [← ZMod.val_natCast_of_lt a.isLt, ← ZMod.val_natCast_of_lt b.isLt,
        mul_left_cancel₀ hl_ne h_zmod])
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj), fun _ ↦ rfl⟩

/-- Reducing an integer matrix modulo a divisor: if `M ≡ 1 (mod m)` and `d ∣ m`, then
`M ≡ 1 (mod d)`. -/
private lemma matrix_intCast_map_eq_one_of_dvd {ι : Type*} [DecidableEq ι]
    {d m : ℕ} (hdm : d ∣ m) {M : Matrix ι ι ℤ}
    (hM : M.map (Int.cast : ℤ → ZMod m) = 1) :
    M.map (Int.cast : ℤ → ZMod d) = 1 := by
  have h_factor : ∀ a : ℤ, ((a : ZMod d)) =
      (ZMod.castHom hdm (ZMod d)) ((a : ZMod m)) := by
    intro a
    exact congr_fun (congr_arg DFunLike.coe (show (Int.castRingHom (ZMod d) : ℤ →+* ZMod d) =
      (ZMod.castHom hdm (ZMod d)).comp (Int.castRingHom (ZMod m)) from Subsingleton.elim _ _)) a
  ext i j
  have h_entry : (((M i j : ℤ) : ZMod m)) = ((1 : Matrix ι ι (ZMod m)) i j) := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun hM i) j
  simp only [Matrix.map_apply]
  rw [h_factor, h_entry]
  by_cases hij : i = j
  · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]

/-- The lower-left entry `γ.val 1 0 / l` of `levelRaiseConjOfDvd l γ` is divisible by `d`
whenever the original entry is divisible by `l * d`. -/
private lemma levelRaiseConjOfDvd_lower_left_dvd
    {p N l : ℕ} [NeZero l] (hp : p.Prime) (hpN : p ∣ N) (hl : (l : ℤ) ≠ 0)
    (γ : SL(2, ℤ)) (hdvd : (l : ℤ) ∣ γ.val 1 0)
    (h : (((l * N) / p : ℕ) : ℤ) ∣ γ.val 1 0) :
    ((N / p : ℕ) : ℤ) ∣ (HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd).val 1 0 := by
  have h_lNp_eq : (l * N) / p = l * (N / p) := by
    rcases hpN with ⟨c, hc⟩
    rw [hc, show l * (p * c) = p * (l * c) by ring,
        Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos]
  have h10_eq : γ.val 1 0 =
      (l : ℤ) * (HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd).val 1 0 := by
    show _ = (l : ℤ) * (γ.val 1 0 / (l : ℤ))
    rw [mul_comm, Int.ediv_mul_cancel hdvd]
  have h_dvd_lNp : ((l * (N / p) : ℕ) : ℤ) ∣ γ.val 1 0 := by
    have hcast : (((l * N) / p : ℕ) : ℤ) = ((l * (N / p) : ℕ) : ℤ) := by exact_mod_cast h_lNp_eq
    exact hcast ▸ h
  obtain ⟨j, hj⟩ := h_dvd_lNp
  refine ⟨j, mul_left_cancel₀ hl ?_⟩
  rw [← h10_eq, hj]
  push_cast
  ring

/-- If `γ ≡ 1 (mod d)` and `d ∣ (γ.val 1 0 / l)`, then `levelRaiseConjOfDvd l γ ≡ 1 (mod d)`. -/
private lemma levelRaiseConjOfDvd_intCast_map_eq_one
    {d l : ℕ} [NeZero l] (γ : SL(2, ℤ)) (hdvd : (l : ℤ) ∣ γ.val 1 0)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod d) = 1)
    (h10 : (d : ℤ) ∣ (HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd).val 1 0) :
    (HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → ZMod d) = 1 := by
  ext i j
  have h00 := congr_fun (congr_fun hγ 0) 0
  have h01 := congr_fun (congr_fun hγ 0) 1
  have h11 := congr_fun (congr_fun hγ 1) 1
  simp only [Matrix.map_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at h00 h01 h11
  have h_val : ∀ a b : Fin 2,
      (HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd : Matrix (Fin 2) (Fin 2) ℤ) a b =
      !![γ.val 0 0, l * γ.val 0 1; γ.val 1 0 / l, γ.val 1 1] a b := fun _ _ ↦ rfl
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map_apply, Matrix.one_apply, Fin.zero_eta, Fin.mk_one,
      h_val, ite_true, Fin.isValue]
  · show ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod d) = 1
    exact h00
  · show (((l : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod d) = 0
    push_cast
    rw [h01, mul_zero]
  · show (((HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd :
        Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod d) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h10
  · show ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod d) = 1
    exact h11

/-- If `a ≡ 1` and `b ≡ 1 (mod d)` in `SL(2, ℤ)`, then `a * b⁻¹ ≡ 1 (mod d)`. -/
private lemma specialLinearGroup_map_intCast_mul_inv_eq_one
    {d : ℕ} (a b : SL(2, ℤ))
    (ha : (a : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod d) = 1)
    (hb : (b : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod d) = 1) :
    ((a * b⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod d) = 1 := by
  let φ : SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod d) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod d))
  have h_φ_def : ∀ γ : SL(2, ℤ),
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod d) = (φ γ).val := by
    intro γ
    ext i j
    rw [map_apply_coe]
    simp [RingHom.mapMatrix_apply]
  rw [h_φ_def, show φ (a * b⁻¹) = φ a * (φ b)⁻¹ from by rw [map_mul, map_inv]]
  have hEq : φ a = φ b := by
    ext i j
    simp only [← h_φ_def]
    exact congr_fun (congr_fun (ha.trans hb.symm) i) j
  rw [hEq, mul_inv_cancel]
  rfl

/-- For `δ = levelRaiseConjOfDvd l γ * γ'⁻¹` with `γ, γ'` both reducing to `!![0,-1;1,0]`
modulo `p`, the entry `δ 0 1` is divisible by `p`. -/
private lemma levelRaiseConj_mul_inv_zero_one_dvd_p
    {p l : ℕ} [NeZero l] (γ γ' : SL(2, ℤ)) (hdvd : (l : ℤ) ∣ γ.val 1 0)
    (hγ_p : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p) = !![0, -1; 1, 0])
    (hγ'_p : (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p) = !![0, -1; 1, 0]) :
    (p : ℤ) ∣ ((HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd * γ'⁻¹ : SL(2, ℤ))
                : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
  set γt := HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd
  have h_γt_00 : ((γt : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) = 0 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun hγ_p 0) 0
  have h_γt_01 : ((γt : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) = -(l : ZMod p) := by
    have h := congr_fun (congr_fun hγ_p 0) 1
    simp [Matrix.map_apply] at h
    show (((l : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod p) = -(l : ZMod p)
    push_cast
    rw [h]
    ring
  have h_inv_11 : ((γ'⁻¹).val 1 1 : ZMod p) = 0 := by
    rw [show ((γ'⁻¹).val 1 1 : ℤ) =
        ((γ' : Matrix (Fin 2) (Fin 2) ℤ).adjugate 1 1) from
      congr_fun (congr_fun (Matrix.SpecialLinearGroup.coe_inv γ') 1) 1,
      Matrix.adjugate_fin_two]
    simpa [Matrix.map_apply] using congr_fun (congr_fun hγ'_p 0) 0
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h_mul_apply : ((γt * γ'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 =
      (γt : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ'⁻¹).val 0 1 +
      (γt : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ'⁻¹).val 1 1 := by
    show (γt.val * γ'⁻¹.val) 0 1 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [h_mul_apply]
  push_cast
  rw [h_γt_00, h_γt_01, h_inv_11]
  ring

/-- The diagonal conjugation identity `D · δ = β · D` for `D = diag(1, p)`, where `β` is `δ`
with its `(0,1)` entry replaced by `k'` (with `δ 0 1 = p · k'`) and its `(1,0)` entry scaled
by `p`. -/
private lemma diag_p_mapGL_conj_eq
    {p : ℕ} (δ β : SL(2, ℤ)) (k' : ℤ)
    (hk' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = (p : ℤ) * k')
    (hβval : (β : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, k';
         (p : ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1])
    (D : GL (Fin 2) ℝ) (hD : (D : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, (p : ℝ)]) :
    D * mapGL ℝ δ = mapGL ℝ β * D := by
  apply Units.ext
  simp only [Units.val_mul, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply]
  rw [hD]
  simp only [hβval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] <;>
    linarith [hk', mul_comm (p : ℝ) (k' : ℝ),
              show ((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) = (p : ℝ) * k' by exact_mod_cast hk']

/-- Conjugating `δ ≡ 1 (mod N/p)` with `p ∣ δ 0 1` by `D = diag(1, p)` yields a matrix
`β ∈ Γ₀(N)` with trivial character and `D · δ = β · D`. -/
private lemma exists_Gamma0_conj_of_delta_mod
    {N p : ℕ} [NeZero N] (hpN : p ∣ N)
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (δ : SL(2, ℤ))
    (hδ_mod_Np : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1)
    (hδ_01_p : (p : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1)
    (D : GL (Fin 2) ℝ) (hD : (D : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, (p : ℝ)]) :
    ∃ (β : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hβ : β ∈ Gamma0 N),
      χ (Gamma0MapUnits ⟨β, hβ⟩) = 1 ∧ D * mapGL ℝ δ = mapGL ℝ β * D := by
  obtain ⟨k', hk'⟩ := hδ_01_p
  let a := (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  let c := (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  let d := (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_det_β : (!![a, k'; (p : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have hdet : (δ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by exact_mod_cast δ.det_coe
    simp only [Matrix.det_fin_two] at hdet
    lia
  let β : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![a, k'; (p : ℤ) * c, d], h_det_β⟩
  have hδ_10_Np : ((N / p : ℕ) : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [Matrix.map_apply, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
      using congr_fun (congr_fun hδ_mod_Np 1) 0
  have hβ_mem : β ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show (((p : ℤ) * c : ℤ) : ZMod N) = 0
    obtain ⟨c', hc'⟩ := hδ_10_Np
    have hpNp_eq_N : ((p : ℤ)) * ((N / p : ℕ) : ℤ) = (N : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hpN
    rw [show c = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 from rfl, hc',
      show (p : ℤ) * (((N / p : ℕ) : ℤ) * c') = (N : ℤ) * c' by rw [← mul_assoc, hpNp_eq_N],
      Int.cast_mul]
    simp
  have h_unitsMap_β :
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpN) (Gamma0MapUnits ⟨β, hβ_mem⟩) = 1 := by
    apply Units.ext
    simp only [ZMod.unitsMap_val, Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk,
      OneHom.coe_mk, Units.val_one]
    rw [ZMod.cast_intCast (Nat.div_dvd_of_dvd hpN)]
    show ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) = 1
    simpa [Matrix.map_apply, Matrix.one_apply_eq] using congr_fun (congr_fun hδ_mod_Np 1) 1
  have h_chi_β : χ (Gamma0MapUnits ⟨β, hβ_mem⟩) = 1 := by
    rw [hχ_eq]
    show (χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) (Gamma0MapUnits ⟨β, hβ_mem⟩) = 1
    simp only [MonoidHom.comp_apply]
    rw [h_unitsMap_β, map_one]
  exact ⟨β, hβ_mem, h_chi_β, diag_p_mapGL_conj_eq δ β k' hk' rfl D hD⟩

lemma m6_2_extra_rep_levelRaise_bridge
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N)
    [NeZero (N / p)]
    (l : ℕ) [NeZero l] (_hpl : Nat.Coprime p l) (_hlNp : l ∣ N / p)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ modFormCharSpace k χ)
    [NeZero (l * N)] [NeZero ((l * N) / p)] (hpN_lN : p ∣ l * N)
    (hp_sq_lN : ¬ p ^ 2 ∣ l * N)
    (hdvd_lN : (l : ℤ) ∣ (descendExtraGamma p (l * N) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ∀ z : UpperHalfPlane,
      ((⇑f ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), 0; 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ)) ∣[k]
          (mapGL ℝ (HeckeRing.GL2.levelRaiseConjOfDvd l (descendExtraGamma p (l * N)) hdvd_lN)
            : GL (Fin 2) ℝ)) z =
      ((⇑f ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), 0; 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ)) ∣[k]
          (mapGL ℝ (descendExtraGamma p N) : GL (Fin 2) ℝ)) z := by
  intro z
  set γ_lN := descendExtraGamma p (l * N)
  set γtilde : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    HeckeRing.GL2.levelRaiseConjOfDvd l γ_lN hdvd_lN
  set γ_N := descendExtraGamma p N
  have h_γ_N_spec := descendExtraGamma_spec hp hpN hp_sq
  have h_γ_lN_spec := descendExtraGamma_spec (p := p) (N := l * N) hp hpN_lN hp_sq_lN
  have h_Np_dvd_lNp : N / p ∣ (l * N) / p := by
    rcases hpN with ⟨c, hc⟩
    exact ⟨l, by rw [hc, show l * (p * c) = p * (l * c) by ring,
      Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos, mul_comm]⟩
  have h_γ_lN_mod_Np :
      (γ_lN : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1 :=
    matrix_intCast_map_eq_one_of_dvd h_Np_dvd_lNp h_γ_lN_spec.2.2
  have h_γ_lN_10_dvd_lNp : (((l * N) / p : ℕ) : ℤ) ∣ (γ_lN : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp h_γ_lN_spec.1)
  have h_γtilde_mod_Np :
      (γtilde : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1 :=
    levelRaiseConjOfDvd_intCast_map_eq_one γ_lN hdvd_lN h_γ_lN_mod_Np
      (levelRaiseConjOfDvd_lower_left_dvd hp hpN (Nat.cast_ne_zero.mpr (NeZero.ne l)) γ_lN hdvd_lN
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp h_γ_lN_spec.1)))
  set δ : Matrix.SpecialLinearGroup (Fin 2) ℤ := γtilde * γ_N⁻¹ with hδ_def
  have hδ_mod_Np : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1 :=
    specialLinearGroup_map_intCast_mul_inv_eq_one γtilde γ_N h_γtilde_mod_Np h_γ_N_spec.2.2
  let D : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![(1 : ℝ), 0; 0, (p : ℝ)]
      (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
  obtain ⟨β, hβ_mem, h_chi_β, hD_δ⟩ :=
    exists_Gamma0_conj_of_delta_mod hpN χ χ' hχ_eq δ hδ_mod_Np
      (levelRaiseConj_mul_inv_zero_one_dvd_p γ_lN γ_N hdvd_lN h_γ_lN_spec.2.1 h_γ_N_spec.2.1) D rfl
  change ((⇑f ∣[k] D) ∣[k] (mapGL ℝ γtilde : GL (Fin 2) ℝ)) z =
      ((⇑f ∣[k] D) ∣[k] (mapGL ℝ γ_N : GL (Fin 2) ℝ)) z
  have h_γtilde_eq : mapGL ℝ γtilde = mapGL ℝ δ * mapGL ℝ γ_N := by
    simp [hδ_def]
  simp_rw [← SlashAction.slash_mul]
  rw [h_γtilde_eq, ← mul_assoc, hD_δ, mul_assoc, SlashAction.slash_mul,
    multipass_modFormCharSpace_slash_apply χ hfχ β hβ_mem]
  simp [h_chi_β]

private lemma multipass_V_p_slash_upper_aux
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) [NeZero (N / p)]
    (g_low : ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k)
    (j : ℕ) (w : UpperHalfPlane) :
    (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low) ∣[k]
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ)) w = (p : ℂ)⁻¹ * g_low w := by
  have h_glMap_eq : (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
      : GL (Fin 2) ℝ) = glMap (T_p_upper p hp.pos j) := by
    apply Units.ext
    ext i k'
    fin_cases i <;> fin_cases k' <;>
      simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        Matrix.GeneralLinearGroup.map, Matrix.map_apply]
  rw [h_glMap_eq]
  change ((⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low)) ∣[k]
      (T_p_upper p hp.pos j : GL (Fin 2) ℚ)) w = _
  rw [HeckeRing.GL2.slash_T_p_upper_eval k p hp j _ w]
  congr 1
  rw [HeckeRing.GL2.modularFormLevelRaise_apply (N / p) p k g_low]
  have h_uhp_eq :
      (HeckeRing.GL2.levelRaiseMatrix p • (⟨(↑w + ↑j) / ↑p,
        by simpa using div_pos (by linarith [w.im_pos]) (Nat.cast_pos.mpr hp.pos)⟩
          : UpperHalfPlane)) =
        (j : ℝ) +ᵥ w := by
    apply UpperHalfPlane.ext
    rw [HeckeRing.GL2.coe_levelRaiseMatrix_smul, UpperHalfPlane.coe_vadd]
    push_cast
    field_simp [Nat.cast_ne_zero.mpr hp.ne_zero]
    ring
  rw [h_uhp_eq]
  apply SlashInvariantForm.vAdd_apply_of_mem_strictPeriods
  rw [show (Gamma1 (N / p)).map (mapGL ℝ) = (Gamma1 (N / p) : Subgroup (GL (Fin 2) ℝ)) from rfl,
    strictPeriods_Gamma1]
  exact ⟨(j : ℤ), by simp⟩

/-- For each `v` in the descent coset list, the slash of `V_p g_low` by the corresponding
coset matrix equals `p⁻¹ * g_low(z)` pointwise. -/
lemma multipass_V_p_slash_descendCoset
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (g_low : ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k)
    (v : Fin (descendCosetCount p N)) (z : UpperHalfPlane) :
    (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low) ∣[k]
      (descendCosetList p N hp v)) z = (p : ℂ)⁻¹ * g_low z := by
  unfold descendCosetList
  split_ifs with h_v
  · exact multipass_V_p_slash_upper_aux p hp g_low v.val z
  · rw [SlashAction.slash_mul]
    have h_inner_fun : ((⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low)) ∣[k]
        (Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(1 : ℝ), 0; 0, (p : ℝ)]
            (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
          : GL (Fin 2) ℝ)) = ((p : ℂ)⁻¹ • ⇑g_low : UpperHalfPlane → ℂ) := by
      ext w
      simpa using multipass_V_p_slash_upper_aux p hp g_low 0 w
    have h_γ_in_Γ1 : descendExtraGamma p N ∈ Gamma1 (N / p) := by
      rw [Gamma1_mem]
      refine ⟨?_, ?_, ?_⟩ <;>
        · simpa [Matrix.map_apply, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
            using congr_fun (congr_fun
              (descendExtraGamma_spec hp hpN (not_p_sq_dvd_of_not_lt h_v)).2.2 _) _
    have h_g_low_inv : (⇑g_low : UpperHalfPlane → ℂ) ∣[k]
        (mapGL ℝ (descendExtraGamma p N) : GL (Fin 2) ℝ) = ⇑g_low :=
      g_low.slash_action_eq' _ ⟨descendExtraGamma p N, h_γ_in_Γ1, rfl⟩
    have h_σ : UpperHalfPlane.σ (mapGL ℝ (descendExtraGamma p N) : GL (Fin 2) ℝ) =
        RingHom.id ℂ :=
      multipass_sigma_eq_id_of_det_pos _ (by simp)
    rw [h_inner_fun, ModularForm.smul_slash, h_σ, RingHom.id_apply, h_g_low_inv]
    simp [Pi.smul_apply, smul_eq_mul]

/-- **H31 (audit-multipass descendCosetList_lift_eq_glMap)**: every coset
matrix `descendCosetList p N hp v : GL (Fin 2) ℝ` admits a rational lift
`A_v : GL (Fin 2) ℚ` with `glMap A_v = descendCosetList p N hp v`.

This is exactly what makes the cusp transport lemma
`glMap_smul_isCusp_Gamma1` (and the inner Hecke operators) applicable to
the descent operator: the lift's existence is the algebraic reason that
the slash sum of a cusp form again has cusp-form-like behaviour.

The lift mirrors the definition of `descendCosetList` entry-wise:
* For `v.val < p`: `[1, v.val; 0, p]` over `ℚ`.
* For the extra rep: `[1, 0; 0, p] · mapGL ℚ γ_p^(p)` over `ℚ`. -/
lemma descendCosetList_lift_eq_glMap
    {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    (v : Fin (descendCosetCount p N)) :
    ∃ A : GL (Fin 2) ℚ, glMap A = descendCosetList p N hp v := by
  unfold descendCosetList
  split_ifs with h_v
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(1 : ℚ), (v.val : ℚ); 0, (p : ℚ)]
        (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero), ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [glMap, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, algebraMap]
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℚ), 0; 0, (p : ℚ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) *
        mapGL ℚ (descendExtraGamma p N), ?_⟩
    rw [map_mul, glMap_mapGL_eq]
    congr 1
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [glMap, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, algebraMap]

/-- **M5a: Explicit GL₂(ℝ) coset reps with the action property** (Miyake,
p. 161, Lemma 4.5.6 and 4.5.11).

For `p` prime dividing `N` with `NeZero (N/p)`, set `d := p − 1` if `p² ∣ N`,
else `d := p`. There exists a `(d+1)`-element list of matrices `γ_v ∈ GL_2(ℝ)`,
each with determinant `p`, satisfying:

* **(Action property at Γ_0(N/p) → Γ_0(N))**: for every
  `γ' ∈ Γ_0(N/p) ⊂ SL_2(ℤ)` (viewed in `GL_2(ℝ)` via `mapGL ℝ`), there
  exist a permutation `σ` of `Fin (d+1)` and matrices `α_v ∈ Γ_0(N)`
  such that `γ_v * mapGL ℝ γ' = mapGL ℝ (α_v) * γ_{σ v}` in `GL_2(ℝ)`.

* **(Diamond compatibility)**: with the action witnesses above, the
  Γ_0(N)-character `Gamma0MapUnits α_v ∈ (ZMod N)ˣ` factors through
  `(ZMod (N/p))ˣ` and equals (the image of) `Gamma0MapUnits γ'` for
  every `v`. -/
theorem miyake_hecke_descend_cosets
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)] :
    (∀ v : Fin (descendCosetCount p N),
      (descendCosetList p N hp v : Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ)) ∧
    ∀ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∀ (h_γ' : γ' ∈ Gamma0 (N / p)),
      ∃ (σ : Equiv.Perm (Fin (descendCosetCount p N)))
        (α : Fin (descendCosetCount p N) → Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (h_mem : ∀ v, α v ∈ Gamma0 N),
        (∀ v, descendCosetList p N hp v * mapGL ℝ γ' =
              mapGL ℝ (α v) * descendCosetList p N hp (σ v)) ∧
        (∀ v, ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)
            (Gamma0MapUnits (N := N) ⟨α v, h_mem v⟩) =
            Gamma0MapUnits (N := N / p) ⟨γ', h_γ'⟩) :=
  ⟨descendCosetList_det p N hp, descendCosetList_action p hp hpN⟩

/-- **M5b**: The slash sum on a `V_p`-lifted form equals the underlying lower-level form
times `p / (descendCosetCount p N)` (Miyake (4.6.12)). -/
theorem miyake_hecke_descend_qexp
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)] :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ (g_low : ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k) (n : ℕ),
        (ModularFormClass.qExpansion (1 : ℝ)
          (fun z ↦ c * ∑ v : Fin (descendCosetCount p N),
            (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low)
              ∣[k] (descendCosetList p N hp v)) z)).coeff n =
        (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff n := by
  have hp_pos : 0 < p := hp.pos
  have hp_ne_C : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_cnt_pos : 0 < descendCosetCount p N := by
    unfold descendCosetCount; split_ifs <;> omega
  have h_cnt_ne_C : (descendCosetCount p N : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h_cnt_pos)
  refine ⟨(p : ℂ) / (descendCosetCount p N : ℂ),
    div_ne_zero hp_ne_C h_cnt_ne_C, fun g_low n ↦ ?_⟩
  suffices h_fun_eq : (fun z : UpperHalfPlane ↦
      (p : ℂ) / (descendCosetCount p N : ℂ) *
      ∑ v : Fin (descendCosetCount p N),
        (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low) ∣[k]
          (descendCosetList p N hp v)) z) = (⇑g_low : UpperHalfPlane → ℂ) by
    rw [h_fun_eq]
  funext z
  rw [Finset.mul_sum]
  have h_each : ∀ v : Fin (descendCosetCount p N),
      (p : ℂ) / (descendCosetCount p N : ℂ) *
        (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low) ∣[k]
          (descendCosetList p N hp v)) z =
      (descendCosetCount p N : ℂ)⁻¹ * g_low z := by
    intro v
    rw [multipass_V_p_slash_descendCoset p hp hpN g_low v z]
    field_simp
  simp_rw [h_each]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma miyake_descent_upper_tri_qExpansion
    {M : ℕ} [NeZero M] (p : ℕ) [NeZero p] (hp : p.Prime) (hpM : p ∣ M)
    {k : ℤ}
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (m : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ)
        (fun z ↦ ∑ v ∈ Finset.range p,
          (⇑g ∣[k] (T_p_upper p hp.pos v : GL (Fin 2) ℚ)) z)).coeff m =
      (ModularFormClass.qExpansion (1 : ℝ) g).coeff (p * m) := by
  have hpM_not_coprime : ¬ Nat.Coprime p M := fun h ↦ hp.coprime_iff_not_dvd.mp h hpM
  have h_fun_eq : (fun z : UpperHalfPlane ↦
      ∑ v ∈ Finset.range p,
        (⇑g ∣[k] (T_p_upper p hp.pos v : GL (Fin 2) ℚ)) z) =
      (⇑(heckeT_p_divN k p hp hpM_not_coprime g) : UpperHalfPlane → ℂ) := by
    funext z
    show ∑ v ∈ Finset.range p,
        (⇑g ∣[k] (T_p_upper p hp.pos v : GL (Fin 2) ℚ)) z =
      heckeT_p_ut k p hp.pos (⇑g) z
    rw [heckeT_p_ut, Finset.sum_apply]
  rw [h_fun_eq]
  exact qExpansion_one_heckeT_p_divN_coeff hp hpM_not_coprime g m

/-- **M5c**: The slash sum `Σ_v ⇑f ∣[k] (descendCosetList p N hp v)` of any cusp form `f`
vanishes at every cusp of `Γ_1(N/p)` (Miyake p. 158). -/
theorem miyake_hecke_descend_cusp
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (_hpN : p ∣ N) [NeZero (N / p)]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∀ {c : OnePoint ℝ}, IsCusp c ((Gamma1 (N / p)).map (mapGL ℝ)) →
      c.IsZeroAt
        (fun z ↦ ∑ v : Fin (descendCosetCount p N),
          (⇑f ∣[k] (descendCosetList p N hp v)) z) k := by
  intro c hc
  have hc_N : IsCusp c ((Gamma1 N).map (mapGL ℝ)) :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z ((Gamma1 N).map (mapGL ℝ))).mpr
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z ((Gamma1 (N / p)).map (mapGL ℝ))).mp hc)
  rw [show (fun z ↦ ∑ v : Fin (descendCosetCount p N),
              (⇑f ∣[k] (descendCosetList p N hp v)) z) =
        ∑ v : Fin (descendCosetCount p N),
              (⇑f ∣[k] (descendCosetList p N hp v)) from
          funext fun z ↦ (Finset.sum_apply z _ _).symm]
  refine Finset.sum_induction _ (fun g ↦ c.IsZeroAt g k)
    (fun _ _ ha hb ↦ ha.add hb)
    ((0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).zero_at_cusps' hc_N) fun v _ ↦ ?_
  obtain ⟨A, hA⟩ := descendCosetList_lift_eq_glMap hp v
  rw [← hA]
  exact OnePoint.IsZeroAt.smul_iff.mp
    (f.zero_at_cusps' (glMap_smul_isCusp_Gamma1 A hc_N))

/-- The orbit identity for the slash sum: slashing the coset sum by `γ_d ∈ Γ₀(N/p)` produces
the reindexed sum `Σ_v (f ∣ α_v) ∣ γ_{σ(v)}` for some permutation `σ` and `Γ₀(N)`-elements
`α_v ∈ Γ₀(N)`. -/
theorem descendCosetList_orbit_identity
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] [NeZero (N / p)]
    (γ : Fin (descendCosetCount p N) → GL (Fin 2) ℝ)
    (h_action : ∀ γ_d : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ_d ∈ Gamma0 (N / p) →
      ∃ (σ : Equiv.Perm (Fin (descendCosetCount p N)))
        (α : Fin (descendCosetCount p N) → Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (_ : ∀ v, α v ∈ Gamma0 N),
        ∀ v, γ v * mapGL ℝ γ_d = mapGL ℝ (α v) * γ (σ v))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ_d : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h_γ_d : γ_d ∈ Gamma0 (N / p)) :
    ∃ (σ : Equiv.Perm (Fin (descendCosetCount p N)))
      (α : Fin (descendCosetCount p N) → Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (_ : ∀ v, α v ∈ Gamma0 N),
      (∀ v, γ v * mapGL ℝ γ_d = mapGL ℝ (α v) * γ (σ v)) ∧
      ((fun z ↦ ∑ v, (⇑f ∣[k] (γ v)) z) ∣[k]
          (mapGL ℝ γ_d : GL (Fin 2) ℝ) : UpperHalfPlane → ℂ) =
        fun z ↦ ∑ v, ((⇑f ∣[k] (mapGL ℝ (α v) : GL (Fin 2) ℝ)) ∣[k] (γ (σ v))) z := by
  obtain ⟨σ, α, h_mem, h_eq⟩ := h_action γ_d h_γ_d
  refine ⟨σ, α, h_mem, h_eq, ?_⟩
  ext z
  rw [show (fun z ↦ ∑ v, (⇑f ∣[k] γ v) z) = ∑ v, ((⇑f) ∣[k] γ v) by
        ext z
        rw [Finset.sum_apply],
      SlashAction.sum_slash, Finset.sum_apply]
  exact Finset.sum_congr rfl fun v _ ↦ by
    rw [← SlashAction.slash_mul, h_eq v, SlashAction.slash_mul]

/-- For `f ∈ modFormCharSpace k χ` with `χ = χ'.comp (ZMod.unitsMap h)`, slashing the coset sum
by `γ_d ∈ Γ₀(N/p)` scales it by `χ'(Gamma0MapUnits ⟨γ_d, _⟩)`. -/
theorem miyake_hecke_descend_char
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hfχ : f ∈ modFormCharSpace k χ) :
    ∀ (γ_d_pair : { γ_d : Matrix.SpecialLinearGroup (Fin 2) ℤ //
                     γ_d ∈ Gamma0 (N / p) }),
      (fun z ↦ ∑ v : Fin (descendCosetCount p N),
        (⇑f ∣[k] (descendCosetList p N hp v)) z) ∣[k]
        (mapGL ℝ γ_d_pair.val : GL (Fin 2) ℝ) =
      ((χ' (Gamma0MapUnits ⟨γ_d_pair.val, γ_d_pair.property⟩) : ℂ) •
        (fun z ↦ ∑ v : Fin (descendCosetCount p N),
          (⇑f ∣[k] (descendCosetList p N hp v)) z) : UpperHalfPlane → ℂ) := by
  intro γ_d_pair
  obtain ⟨γ_d, h_γ_d⟩ := γ_d_pair
  obtain ⟨σ, α, h_α_mem, h_action_eq, h_diamond⟩ :=
      descendCosetList_action p hp hpN γ_d h_γ_d
  have h_chi_eq : ∀ v,
      (χ (Gamma0MapUnits ⟨α v, h_α_mem v⟩) : ℂ) =
        (χ' (Gamma0MapUnits ⟨γ_d, h_γ_d⟩) : ℂ) := by
    intro v
    have : χ (Gamma0MapUnits ⟨α v, h_α_mem v⟩) =
        χ' (Gamma0MapUnits ⟨γ_d, h_γ_d⟩) := by
      rw [hχ_eq, MonoidHom.comp_apply, h_diamond v]
    exact_mod_cast congr_arg ((↑·) : ℂˣ → ℂ) this
  have h_det_pos : ∀ w : Fin (descendCosetCount p N),
      (0 : ℝ) < (descendCosetList p N hp w).det.val := by
    intro w
    rw [Matrix.GeneralLinearGroup.val_det_apply, descendCosetList_det p N hp w]
    exact_mod_cast hp.pos
  ext z
  have h_sum_form : (fun z' : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p N),
      (⇑f ∣[k] descendCosetList p N hp v) z') =
      (∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v)) := by
    ext z'
    rw [Finset.sum_apply]
  rw [h_sum_form, SlashAction.sum_slash, Pi.smul_apply, Finset.sum_apply, Finset.sum_apply,
    (Equiv.sum_comp σ (fun v ↦ (⇑f ∣[k] descendCosetList p N hp v) z)).symm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [(SlashAction.slash_mul k _ _ _).symm, h_action_eq v, SlashAction.slash_mul,
      multipass_modFormCharSpace_slash_apply χ hfχ (α v) (h_α_mem v),
      ModularForm.smul_slash, multipass_sigma_eq_id_of_det_pos _ (h_det_pos (σ v)),
      RingHom.id_apply]
  simp only [Pi.smul_apply, smul_eq_mul, h_chi_eq v]

lemma miyake_hecke_descend_Gamma1_inv
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hfχ : f ∈ modFormCharSpace k χ)
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma1 (N / p)) :
    (fun z ↦ ∑ v : Fin (descendCosetCount p N),
      (⇑f ∣[k] descendCosetList p N hp v) z) ∣[k] (mapGL ℝ γ' : GL (Fin 2) ℝ) =
    fun z ↦ ∑ v : Fin (descendCosetCount p N),
      (⇑f ∣[k] descendCosetList p N hp v) z := by
  obtain ⟨h_γ'_Gamma0, h_units_one⟩ := multipass_char_trivial_on_Gamma1 γ' h_γ'
  have h_char := miyake_hecke_descend_char p hp hpN χ χ' hχ_eq hfχ ⟨γ', h_γ'_Gamma0⟩
  rw [h_units_one, map_one] at h_char
  simpa only [Units.val_one, one_smul] using h_char

private lemma miyake_descend_slash_holo
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v)) :=
  MDifferentiable.sum fun _ _ ↦ (ModularFormClass.holo f).slash k _

private lemma miyake_descend_slash_bddCusps
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) [NeZero (N / p)]
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    {cusp : OnePoint ℝ} (hc : IsCusp cusp ((Gamma1 (N / p)).map (mapGL ℝ))) :
    cusp.IsBoundedAt
      (∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v)) k := by
  have hc_N : IsCusp cusp ((Gamma1 N).map (mapGL ℝ)) :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)
  refine Finset.sum_induction _ (fun g ↦ cusp.IsBoundedAt g k)
    (fun _ _ ha hb ↦ ha.add hb)
    ((0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k).bdd_at_cusps' hc_N) fun v _ ↦ ?_
  obtain ⟨A, hA⟩ := descendCosetList_lift_eq_glMap hp v
  rw [← hA]
  exact OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' (glMap_smul_isCusp_Gamma1 A hc_N))

private lemma miyake_descend_slash_smul
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (s : ℂ) (f : UpperHalfPlane → ℂ)
    (v : Fin (descendCosetCount p N)) :
    (s • f) ∣[k] descendCosetList p N hp v = s • (f ∣[k] descendCosetList p N hp v) := by
  have h_det : (0 : ℝ) < (descendCosetList p N hp v).det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, descendCosetList_det p N hp v]
    exact_mod_cast hp.pos
  rw [ModularForm.smul_slash, multipass_sigma_eq_id_of_det_pos _ h_det, RingHom.id_apply]

private lemma miyake_hecke_descend_lifted_coe_eq
    (k : ℤ) {M N : ℕ} (h : M = N)
    (G : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (⇑(h ▸ G : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) = ⇑G := by
  subst h; rfl

private lemma miyake_hecke_descend_slashSum_eq
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (fun z ↦ ∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v) z) =
      ∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v) :=
  funext fun _ ↦ (Finset.sum_apply _ _ _).symm

private noncomputable def miyake_hecke_descend_modForm
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hfχ : f ∈ modFormCharSpace k χ) :
    ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k where
  toFun := fun z ↦ ∑ v : Fin (descendCosetCount p N),
    (⇑f ∣[k] descendCosetList p N hp v) z
  slash_action_eq' γ hγ := by
    obtain ⟨γ', h_γ'_Gamma1, rfl⟩ := Subgroup.mem_map.mp hγ
    exact miyake_hecke_descend_Gamma1_inv p hp hpN χ χ' hχ_eq hfχ γ' h_γ'_Gamma1
  holo' := by
    simp only [SlashInvariantForm.coe_mk, miyake_hecke_descend_slashSum_eq]
    exact miyake_descend_slash_holo p hp f
  bdd_at_cusps' {_} hc := by
    rw [miyake_hecke_descend_slashSum_eq p hp f]
    exact miyake_descend_slash_bddCusps p hp f hc

private lemma miyake_hecke_descend_modForm_mem
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hfχ : f ∈ modFormCharSpace k χ) :
    miyake_hecke_descend_modForm p hp hpN χ χ' hχ_eq f hfχ ∈ modFormCharSpace k χ' := by
  rw [mem_modFormCharSpace_iff]
  intro d
  obtain ⟨g_rep, h_g_rep⟩ := HeckeRing.GL2.Gamma0MapUnits_surjective (N := N / p) d
  have h_g_eq : HeckeRing.GL2.Gamma0MapUnits
      ⟨(g_rep : Matrix.SpecialLinearGroup (Fin 2) ℤ), g_rep.property⟩ = d := by
    simpa [HeckeRing.GL2.Gamma0MapUnits] using h_g_rep
  have h_char := miyake_hecke_descend_char p hp hpN χ χ' hχ_eq hfχ ⟨g_rep, g_rep.property⟩
  rw [h_g_eq] at h_char
  rw [show HeckeRing.GL2.diamondOpHom (N := N / p) k d _ =
      HeckeRing.GL2.diamondOpAux (N := N / p) k g_rep _ from
    congrFun (congrArg _ (HeckeRing.GL2.diamondOp_eq_diamondOpAux (N := N / p) k d g_rep h_g_rep))
      _]
  exact ModularForm.ext fun z ↦ congrFun h_char z

private noncomputable def miyake_hecke_descend_linearMap
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) :
    modFormCharSpace k χ →ₗ[ℂ] modFormCharSpace k χ' where
  toFun := fun ⟨f, hfχ⟩ ↦
    ⟨miyake_hecke_descend_modForm p hp hpN χ χ' hχ_eq f hfχ,
     miyake_hecke_descend_modForm_mem p hp hpN χ χ' hχ_eq f hfχ⟩
  map_add' := fun ⟨f, _⟩ ⟨g, _⟩ ↦ Subtype.val_injective <| by
    ext z
    simp only [Submodule.coe_add]
    change ∑ v : Fin (descendCosetCount p N), (⇑(f + g) ∣[k] descendCosetList p N hp v) z =
        ∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v) z +
        ∑ v : Fin (descendCosetCount p N), (⇑g ∣[k] descendCosetList p N hp v) z
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ ↦
      congrFun (SlashAction.add_slash k (descendCosetList p N hp v) (⇑f) (⇑g)) z
  map_smul' := fun s ⟨f, _⟩ ↦ Subtype.val_injective <| by
    ext z
    simp only [Submodule.coe_smul, RingHom.id_apply]
    change ∑ v : Fin (descendCosetCount p N), (⇑(s • f) ∣[k] descendCosetList p N hp v) z =
        s • ∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v) z
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun v _ ↦
      congrFun (miyake_descend_slash_smul p hp s (⇑f) v) z

/-- Existence of the Hecke descent linear map `Φ : modFormCharSpace k χ →ₗ[ℂ] modFormCharSpace k χ'`
(Miyake §4.6), together with cusp-form preservation and the `Φ ∘ V_p = c · id` identity. -/
theorem miyake_hecke_descend
    {N : ℕ} [NeZero N] (k : ℤ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) :
    ∃ (Φ : modFormCharSpace k χ →ₗ[ℂ] modFormCharSpace k χ')
      (c : ℂ),
      (∀ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
          (hfχ : f.toModularForm' ∈ modFormCharSpace k χ)
          {cusp : OnePoint ℝ},
            IsCusp cusp ((Gamma1 (N / p)).map (mapGL ℝ)) →
            cusp.IsZeroAt (Φ ⟨f.toModularForm', hfχ⟩).val.toFun k) ∧
      c ≠ 0 ∧
      ∀ (g_low : modFormCharSpace k χ') (n : ℕ)
        (h_lift_eq : p * (N / p) = N) (h_mem : h_lift_eq ▸
            HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low.val ∈ modFormCharSpace k χ),
        (ModularFormClass.qExpansion (1 : ℝ)
          (Φ ⟨h_lift_eq ▸ HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low.val,
               h_mem⟩).val).coeff n =
        c * (ModularFormClass.qExpansion (1 : ℝ) g_low.val).coeff n := by
  obtain ⟨c_qexp, hc_qexp_ne, h_qexp⟩ := miyake_hecke_descend_qexp (N := N) p hp hpN
  refine ⟨miyake_hecke_descend_linearMap p hp hpN χ χ' hχ_eq, c_qexp⁻¹,
    fun f _ {_} hc ↦ miyake_hecke_descend_cusp p hp hpN f hc,
    inv_ne_zero hc_qexp_ne, ?_⟩
  intro ⟨g_low, _⟩ n h_lift_eq h_mem
  set G := HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low
  set g_lifted := h_lift_eq ▸ G
  set S : UpperHalfPlane → ℂ :=
    fun z ↦ ∑ v : Fin (descendCosetCount p N), (⇑G ∣[k] descendCosetList p N hp v) z
  have hcoe : (⇑g_lifted : UpperHalfPlane → ℂ) = ⇑G :=
    miyake_hecke_descend_lifted_coe_eq k h_lift_eq G
  have hRHS : S =
      ⇑(miyake_hecke_descend_linearMap p hp hpN χ χ' hχ_eq ⟨g_lifted, h_mem⟩).val :=
    funext fun z ↦ by
      show _ = ∑ v : Fin (descendCosetCount p N), (⇑g_lifted ∣[k] descendCosetList p N hp v) z
      simp [hcoe, S]
  have h_factor : (PowerSeries.coeff n)
      (ModularFormClass.qExpansion 1 (c_qexp • S)) =
      c_qexp * (PowerSeries.coeff n) (ModularFormClass.qExpansion 1 S) := by
    have h1_period : (1 : ℝ) ∈ ((Gamma1 (N / p)).map (mapGL ℝ)).strictPeriods := by
      rw [show (Gamma1 (N / p)).map (mapGL ℝ) =
          (Gamma1 (N / p) : Subgroup (GL (Fin 2) ℝ)) from rfl, strictPeriods_Gamma1]
      exact ⟨1, by simp⟩
    rw [hRHS, qExpansion_smul one_pos h1_period, PowerSeries.coeff_smul, smul_eq_mul]
  rw [← hRHS]
  field_simp [hc_qexp_ne]
  linear_combination h_factor.symm.trans (h_qexp g_low n)

end HeckeRing.GL2
