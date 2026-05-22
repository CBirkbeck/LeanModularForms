/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.Presentation

/-!
# Hecke Ring for Congruence Subgroups (Shimura §3.3) — Degree combinatorics

Chinese-remainder degree multiplicativity for `Γ₀(N)` double cosets:
the diagonal stabilizer identification (`stab_diag_eq_Gamma0`), the coprime
degree multiplicativity `Gamma0_deg_coprime_mul`, and the prime-power degree
formulas (`HeckeCoset_deg_Gamma0_one_ppow`, `HeckeCoset_deg_Gamma0_p_ppow`).

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.2–3.3
-/

open Matrix Subgroup.Commensurable Pointwise Matrix.SpecialLinearGroup

open scoped Pointwise MatrixGroups

namespace HeckeRing.GLn
/-! #### Gamma0 degree coprime multiplicativity: CRT helpers -/

/-- The (1,0) entry of `diag(1,k)⁻¹ * σ * diag(1,k)` is `σ₁₀ / k` in ℚ.
This is the key entry computation for diagonal stabilizer identification. -/
private lemma diagConj_10 (k : ℕ) (hk : 0 < k) (σ : GL (Fin 2) ℚ) :
    ((diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ)⁻¹ * σ *
      (diagMat 2 (![1, k] : Fin 2 → ℕ))).1 1 0 = σ.1 1 0 / k := by
  have hk_ne : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hk_pos : ∀ i : Fin 2, 0 < (![1, k] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hk]
  have h_diag_val : (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ).val =
      !![(1 : ℚ), 0; 0, (k : ℚ)] := by
    ext i j
    rw [diagMat_val 2 _ hk_pos]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  have h_diag_inv_val : ((diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ)⁻¹).val =
      !![(1 : ℚ), 0; 0, (1 : ℚ) / k] := by
    rw [Matrix.coe_units_inv, h_diag_val, Matrix.inv_def, Matrix.adjugate_fin_two,
      Ring.inverse_eq_inv']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two_of] <;> field_simp
  rw [Units.val_mul, Units.val_mul, h_diag_inv_val, h_diag_val]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const]
  field_simp
  ring

/-- **CRT card formula for subgroup quotients**: if `K₁ ⊓ K₂ = L` and every element
of `G` factors as `k₁ * k₂`, then `|G/L| = |G/K₁| * |G/K₂|`. -/
private lemma card_quotient_inf_of_set_mul {G : Type*} [Group G]
    (K₁ K₂ : Subgroup G) [K₁.FiniteIndex] [K₂.FiniteIndex] [(K₁ ⊓ K₂).FiniteIndex]
    (h_prod : ∀ g : G, ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, g = k₁ * k₂) :
    Nat.card (G ⧸ (K₁ ⊓ K₂)) = Nat.card (G ⧸ K₁) * Nat.card (G ⧸ K₂) := by
  set f : G ⧸ (K₁ ⊓ K₂) → (G ⧸ K₁) × (G ⧸ K₂) :=
    Quotient.lift (fun g => (QuotientGroup.mk g, QuotientGroup.mk g))
      (fun a b hab => by
        have hmem := QuotientGroup.leftRel_apply.mp hab
        exact Prod.ext (QuotientGroup.eq.mpr (Subgroup.mem_inf.mp hmem).1)
          (QuotientGroup.eq.mpr (Subgroup.mem_inf.mp hmem).2))
  have hf_inj : Function.Injective f := by
    intro a b; refine Quotient.inductionOn₂ a b (fun x y h => ?_)
    simp only [f, Quotient.lift_mk] at h
    have h1 := QuotientGroup.eq.mp (Prod.ext_iff.mp h).1
    have h2 := QuotientGroup.eq.mp (Prod.ext_iff.mp h).2
    exact QuotientGroup.eq.mpr (Subgroup.mem_inf.mpr ⟨h1, h2⟩)
  have hf_surj : Function.Surjective f := by
    rintro ⟨a, b⟩; refine Quotient.inductionOn₂ a b (fun α β => ?_)
    obtain ⟨k₁, hk₁, k₂, hk₂, h_eq⟩ := h_prod (α⁻¹ * β)
    refine ⟨QuotientGroup.mk (α * k₁), Prod.ext ?_ ?_⟩
    · apply QuotientGroup.eq.mpr
      show (α * k₁)⁻¹ * α ∈ K₁
      have : (α * k₁)⁻¹ * α = k₁⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ hk₁
    · apply QuotientGroup.eq.mpr
      show (α * k₁)⁻¹ * β ∈ K₂
      have step1 : (α * k₁)⁻¹ * β = k₁⁻¹ * (α⁻¹ * β) := by group
      rw [step1, h_eq]
      have step2 : k₁⁻¹ * (k₁ * k₂) = k₂ := by group
      rw [step2]; exact hk₂
  rw [← Nat.card_prod]
  exact Nat.card_eq_of_bijective _ ⟨hf_inj, hf_surj⟩

open CongruenceSubgroup in
/-- `Γ₀(mN) ⊓ Γ₀(nN) = Γ₀(mnN)` when `gcd(m,n) = 1`. -/
private lemma Gamma0_inf_eq_of_coprime (N m n : ℕ) [NeZero N] [NeZero (m * N)] [NeZero (n * N)]
    [NeZero (m * n * N)] (hcop : Nat.Coprime m n) :
    Gamma0 (m * N) ⊓ Gamma0 (n * N) = Gamma0 (m * n * N) := by
  have hN_ne : (↑N : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hcop_int : IsCoprime (↑m : ℤ) (↑n : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simp only [Int.gcd, Int.natAbs_natCast]; exact hcop)
  ext g; simp only [Subgroup.mem_inf, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  set c := (g 1 0 : ℤ)
  constructor
  · rintro ⟨hmN, hnN⟩
    have hN_dvd : (↑N : ℤ) ∣ c := dvd_trans (dvd_mul_left (↑N : ℤ) ↑m) hmN
    obtain ⟨q, hq⟩ := hN_dvd
    have hm : (↑m : ℤ) ∣ q := by
      rw [hq, show (↑(m * N) : ℤ) = ↑N * ↑m from by push_cast; ring] at hmN
      exact (mul_dvd_mul_iff_left hN_ne).mp hmN
    have hn : (↑n : ℤ) ∣ q := by
      rw [hq, show (↑(n * N) : ℤ) = ↑N * ↑n from by push_cast; ring] at hnN
      exact (mul_dvd_mul_iff_left hN_ne).mp hnN
    obtain ⟨r, hr⟩ := hcop_int.mul_dvd hm hn
    exact ⟨r, by rw [hq, hr]; push_cast; ring⟩
  · rintro ⟨r, hr⟩
    exact ⟨⟨n * r, by rw [hr]; push_cast; ring⟩,
           ⟨m * r, by rw [hr]; push_cast; ring⟩⟩

/-- For `IsCoprime d N` and `IsCoprime d s`, there exists `b₁` with
`Int.gcd (N*s*b₁ − d) m = 1`. Per prime `p | m`: if `p | d` then `p ∤ Ns` (from
coprimality), so any `b₁ ≢ 0 (mod p)` works; if `p ∤ d` then avoid the single
bad class `b₁ ≡ d·(Ns)⁻¹ (mod p)`. CRT over prime factors gives a valid `b₁`. -/
private lemma exists_coprime_shift (N s d : ℤ) (m : ℕ) (hm_pos : 0 < m)
    (hdN : IsCoprime d N) (hds : IsCoprime d s) :
    ∃ b₁ : ℤ, Int.gcd (N * s * b₁ - d) m = 1 := by
  have hdNs : IsCoprime d (N * s) := hdN.mul_right hds
  set f := N * s
  -- Lift to IsCoprime (cleaner API than Int.gcd).
  suffices ∃ b₁ : ℤ, IsCoprime (f * b₁ - d) (↑m : ℤ) by
    obtain ⟨b₁, h⟩ := this; exact ⟨b₁, Int.isCoprime_iff_gcd_eq_one.mp h⟩
  -- Helper: adding a y-multiple preserves IsCoprime to y.
  have add_mul_coprime : ∀ {x y : ℤ} (z : ℤ), IsCoprime x y → IsCoprime (x + y * z) y := by
    intro x y z ⟨u, v, huv⟩; exact ⟨u, v - z * u, by linear_combination huv⟩
  -- Induction on m via prime-power × coprime decomposition.
  revert hm_pos; refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ m
  · -- Prime power: p^n. Suffices to find b₁ with IsCoprime (f*b₁ - d) p.
    intro p n hp hn _
    have hp_int : Prime (↑p : ℤ) := Nat.prime_iff_prime_int.mp hp
    suffices ∃ b₁, IsCoprime (f * b₁ - d) (↑p : ℤ) from
      this.imp fun b₁ h => h.pow_right
    by_cases hpd : (↑p : ℤ) ∣ d
    · -- p | d ⟹ p ∤ f (from IsCoprime d f). Take b₁=1: p ∤ f, p | d ⟹ p ∤ (f-d).
      have hpf : ¬(↑p : ℤ) ∣ f := by
        rw [← hp_int.coprime_iff_not_dvd, isCoprime_comm]
        exact (hdNs.of_isCoprime_of_dvd_left hpd).symm
      exact ⟨1, by
        rw [mul_one, isCoprime_comm, hp_int.coprime_iff_not_dvd]
        intro h; exact hpf (by have := dvd_add h hpd; rwa [sub_add_cancel] at this)⟩
    · -- p ∤ d. Take b₁ = 0: -d coprime to p.
      exact ⟨0, by
        simp only [mul_zero, zero_sub]
        rw [isCoprime_comm, hp_int.coprime_iff_not_dvd, dvd_neg]
        exact hpd⟩
  · intro h; omega  -- m = 0: excluded
  · exact fun _ => ⟨0, by simp [isCoprime_one_right]⟩  -- m = 1
  · intro a b ha hb hab iha ihb _
    obtain ⟨ba, hba⟩ := iha (by omega)
    obtain ⟨bb, hbb⟩ := ihb (by omega)
    -- CRT witness: b₁ = ba*b*v + bb*a*u where a*u + b*v = 1 (huv).
    have hab_int : IsCoprime (↑a : ℤ) (↑b : ℤ) := by exact_mod_cast hab
    obtain ⟨u, v, huv⟩ := hab_int
    refine ⟨ba * ↑b * v + bb * ↑a * u, ?_⟩
    have hkey : f * (ba * ↑b * v + bb * ↑a * u) - d =
        (f * ba - d) * (↑b * v) + (f * bb - d) * (↑a * u) := by
      linear_combination d * huv
    rw [show (↑(a * b) : ℤ) = ↑a * ↑b from by push_cast; ring, hkey]
    have hbv_a : IsCoprime (↑a : ℤ) (↑b * v) := ⟨u, 1, by linear_combination huv⟩
    have hau_b : IsCoprime (↑b : ℤ) (↑a * u) := ⟨v, 1, by linear_combination huv⟩
    apply IsCoprime.mul_right
    · rw [show (f * ba - d) * (↑b * v) + (f * bb - d) * (↑a * u) =
        (f * ba - d) * (↑b * v) + ↑a * ((f * bb - d) * u) from by ring]
      exact add_mul_coprime _ (isCoprime_comm.mp ((isCoprime_comm.mp hba).mul_right hbv_a))
    · rw [show (f * ba - d) * (↑b * v) + (f * bb - d) * (↑a * u) =
        (f * bb - d) * (↑a * u) + ↑b * (v * (f * ba - d)) from by ring]
      exact add_mul_coprime _ (isCoprime_comm.mp ((isCoprime_comm.mp hbb).mul_right hau_b))

open CongruenceSubgroup in
/-- **`Γ₀(mN) · Γ(N) = Γ₀(N)`**: every `γ ∈ Γ₀(N)` factors as `σ · δ` with
`σ ∈ Γ₀(mN)`, `δ ∈ Γ(N)`. Uses `δ = [[1,Nb₁],[Nc₁,1+N²b₁c₁]] ∈ Γ(N)` (product
of lower/upper unipotent), choosing `b₁` via `exists_coprime_shift` so that
`gcd(Nsb₁−d, m) = 1`, then `c₁` so `m | (s + Nsb₁c₁ − dc₁)`. -/
private lemma Gamma0_mN_mul_GammaN_eq_Gamma0 (N m : ℕ) [NeZero N] [NeZero (m * N)]
    (hm_pos : 0 < m) :
    ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N →
    ∃ σ : SL(2, ℤ), σ ∈ Gamma0 (m * N) ∧ σ⁻¹ * γ ∈ Gamma N := by
  intro γ hγ
  refine SpecialLinearGroup.fin_two_induction
    (P := fun g => g ∈ Gamma0 N →
      ∃ σ : SL(2, ℤ), σ ∈ Gamma0 (m * N) ∧ σ⁻¹ * g ∈ Gamma N) ?_ γ hγ
  clear hγ γ
  intro a b c d hdet hγ
  have hNc : (↑N : ℤ) ∣ c := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
    simpa [Matrix.cons_val_one, Matrix.head_cons] using hγ
  obtain ⟨s, hs⟩ := hNc
  have hd_N : IsCoprime d (↑N : ℤ) := ⟨a, -b * s, by linarith [hs ▸ hdet]⟩
  have hd_s : IsCoprime d s := ⟨a, -b * ↑N, by linarith [hs ▸ hdet]⟩
  obtain ⟨b₁, hb₁⟩ := exists_coprime_shift (↑N * ↑N) s d m hm_pos (hd_N.mul_right hd_N) hd_s
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hb₁
  set c₁ := -s * u
  have hσ10 : ↑N * s * (1 + ↑N * ↑N * b₁ * c₁) - d * (↑N * c₁) = ↑N * (s * ↑m * v) := by
    show ↑N * s * (1 + ↑N * ↑N * b₁ * c₁) - d * (↑N * (-s * u)) = ↑N * (s * ↑m * v)
    linear_combination (-↑N * s) * huv
  set σ₀₀ := a * (1 + ↑N * ↑N * b₁ * c₁) - b * (↑N * c₁)
  set σ₀₁ := b - a * (↑N * b₁)
  set σ₁₀ := ↑N * (s * ↑m * v)
  set σ₁₁ := d - ↑N * ↑N * s * b₁
  have hσ_det : σ₀₀ * σ₁₁ - σ₀₁ * σ₁₀ = 1 := by
    simp only [σ₀₀, σ₀₁, σ₁₀, σ₁₁]
    linear_combination -↑N * s * (b - a * ↑N * b₁) * huv + b * hs + hdet
  set σ : SL(2, ℤ) := ⟨!![σ₀₀, σ₀₁; σ₁₀, σ₁₁], by rwa [Matrix.det_fin_two_of]⟩
  refine ⟨σ, ?_, ?_⟩
  · rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    show (↑(m * N) : ℤ) ∣ σ₁₀
    exact ⟨s * v, by simp [σ₁₀]; ring⟩
  · rw [Gamma_mem']
    have hc_cast : (↑c : ZMod N) = 0 := by
      rw [hs]; push_cast; simp [ZMod.natCast_self]
    have hmod : (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) σ =
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)))
          ⟨!![a, b; c, d], by rwa [Matrix.det_fin_two_of]⟩ := by
      ext i j
      simp only [σ, σ₀₀, σ₀₁, σ₁₀, σ₁₁, SL_reduction_mod_hom_val,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.head_cons, Matrix.head_fin_const]
      fin_cases i <;> fin_cases j <;> push_cast <;>
        simp [ZMod.natCast_self, hc_cast] <;> ring
    rw [map_mul, map_inv, hmod, inv_mul_cancel]

/-- The (i,j) entry of `diag(1,k)⁻¹ * σ * diag(1,k)` at each index. -/
private lemma diagConj_entry (k : ℕ) (hk : 0 < k) (σ : GL (Fin 2) ℚ) (i j : Fin 2) :
    ((diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ)⁻¹ * σ *
      (diagMat 2 (![1, k] : Fin 2 → ℕ))).val i j =
    !![σ.1 0 0, (k : ℚ) * σ.1 0 1;
       σ.1 1 0 / (k : ℚ), σ.1 1 1] i j := by
  have hk_ne : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hk_pos : ∀ i : Fin 2, 0 < (![1, k] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hk]
  have h_diag_val : (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ).val =
      !![(1 : ℚ), 0; 0, (k : ℚ)] := by
    ext i j
    rw [diagMat_val 2 _ hk_pos]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  have h_diag_inv_val : ((diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ)⁻¹).val =
      !![(1 : ℚ), 0; 0, (1 : ℚ) / k] := by
    rw [Matrix.coe_units_inv, h_diag_val, Matrix.inv_def, Matrix.adjugate_fin_two,
      Ring.inverse_eq_inv']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two_of] <;> field_simp
  rw [Units.val_mul, Units.val_mul, h_diag_inv_val, h_diag_val, Matrix.mul_apply,
    Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp only [show ((1 : Fin 2) : ℕ) = 1 from rfl, Fin.zero_eta, Fin.mk_one,
      Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const] <;>
    field_simp <;> ring

/-- **Diagonal stabilizer = Γ₀(kN)**: for the Hecke pair `(Γ₀(N), Δ₀(N))` and a
diagonal element `diag(1,k)`, the double-coset stabilizer
`(ConjAct g • H).subgroupOf H` inside `H = Γ₀(N).map(mapGL)` equals
`Γ₀(kN).map(mapGL).subgroupOf H`. -/
lemma stab_diag_eq_Gamma0 (N : ℕ) [NeZero N] (k : ℕ) (hk : 0 < k) :
    (ConjAct.toConjAct (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ) •
      (Gamma0_pair N).H).subgroupOf (Gamma0_pair N).H =
    ((CongruenceSubgroup.Gamma0 (k * N)).map (mapGL ℚ)).subgroupOf
      (Gamma0_pair N).H := by
  ext ⟨γ, hγ_H⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  obtain ⟨σ, hσ_mem, hσ_eq⟩ := Subgroup.mem_map.mp hγ_H
  have hk_ne_q : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hk_ne_z : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk.ne'
  have h_N_dvd_σ10 : (N : ℤ) ∣ σ.1 1 0 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hσ_mem
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ_mem
  constructor
  · intro h_conj
    obtain ⟨τ, hτ_mem, hτ_eq⟩ := Subgroup.mem_map.mp h_conj
    refine Subgroup.mem_map.mpr ⟨σ, ?_, hσ_eq⟩
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h_val_eq : (mapGL ℚ τ).val = ((diagMat 2 (![1, k] : Fin 2 → ℕ) : GL _ ℚ)⁻¹ *
        mapGL ℚ σ * diagMat 2 (![1, k] : Fin 2 → ℕ)).val := by
      rw [hτ_eq, hσ_eq]
    have h_10_eq : (mapGL ℚ τ).val 1 0 = ((diagMat 2 (![1, k] : Fin 2 → ℕ) : GL _ ℚ)⁻¹ *
        mapGL ℚ σ * diagMat 2 (![1, k] : Fin 2 → ℕ)).val 1 0 := by rw [h_val_eq]
    rw [diagConj_entry k hk (mapGL ℚ σ) 1 0] at h_10_eq
    have h_lhs : (mapGL ℚ τ).val 1 0 = ((τ.1 1 0 : ℤ) : ℚ) := by
      simp [mapGL_coe_matrix, algebraMap_int_eq]
    have h_rhs : ((mapGL ℚ σ).val 1 0) = ((σ.1 1 0 : ℤ) : ℚ) := by
      simp [mapGL_coe_matrix, algebraMap_int_eq]
    have h_10 : ((τ.1 1 0 : ℤ) : ℚ) = ((σ.1 1 0 : ℤ) : ℚ) / (k : ℚ) := by
      rw [← h_lhs, h_10_eq]
      simp [h_rhs]
    have hk_div_σ10 : (k : ℤ) ∣ σ.1 1 0 := by
      have h_div : σ.1 1 0 = k * τ.1 1 0 := by
        have : ((σ.1 1 0 : ℤ) : ℚ) = (k : ℚ) * ((τ.1 1 0 : ℤ) : ℚ) := by
          rw [h_10]; field_simp
        exact_mod_cast this
      exact ⟨τ.1 1 0, h_div⟩
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hτ_mem
    have hN_dvd_τ10 : (N : ℤ) ∣ τ.1 1 0 := by simpa using hτ_mem
    obtain ⟨q, hq⟩ := hk_div_σ10
    have hq_τ : q = τ.1 1 0 := by
      have h1 : (k : ℤ) * q = (k : ℤ) * τ.1 1 0 := by
        rw [← hq]
        have : ((σ.1 1 0 : ℤ) : ℚ) = (k : ℚ) * ((τ.1 1 0 : ℤ) : ℚ) := by
          rw [h_10]; field_simp
        exact_mod_cast this
      exact mul_left_cancel₀ hk_ne_z h1
    have hN_dvd_q : (N : ℤ) ∣ q := hq_τ ▸ hN_dvd_τ10
    obtain ⟨r, hr⟩ := hN_dvd_q
    exact ⟨r, by rw [hq, hr]; push_cast; ring⟩
  · intro h_σ_kN
    obtain ⟨σ', hσ'_mem, hσ'_eq⟩ := Subgroup.mem_map.mp h_σ_kN
    have hσ_eq_σ' : σ = σ' := mapGL_injective (hσ_eq.trans hσ'_eq.symm)
    subst hσ_eq_σ'
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ'_mem
    have hkN_dvd : (↑(k * N) : ℤ) ∣ σ.1 1 0 := by simpa using hσ'_mem
    have hk_dvd : (k : ℤ) ∣ σ.1 1 0 :=
      dvd_trans (show (k : ℤ) ∣ (↑(k * N) : ℤ) from by push_cast; exact dvd_mul_right _ _) hkN_dvd
    obtain ⟨q, hq⟩ := hk_dvd
    have hN_q : (N : ℤ) ∣ q := by
      obtain ⟨r, hr⟩ := hkN_dvd
      have heq : (k : ℤ) * q = (↑(k * N) : ℤ) * r := hq ▸ hr
      rw [show (↑(k * N) : ℤ) = (k : ℤ) * (N : ℤ) from by push_cast; ring] at heq
      rw [mul_assoc] at heq
      exact ⟨r, mul_left_cancel₀ hk_ne_z heq⟩
    have h_det : σ.1 0 0 * σ.1 1 1 - (k * σ.1 0 1) * q = 1 := by
      have hdet := σ.2
      rw [Matrix.det_fin_two] at hdet
      have hq' : σ.1 1 0 = k * q := hq
      linear_combination hdet + σ.1 0 1 * hq'
    set τ : SL(2, ℤ) := ⟨!![σ.1 0 0, k * σ.1 0 1; q, σ.1 1 1], by
      rw [Matrix.det_fin_two_of]; linarith [h_det]⟩ with hτ_def
    refine Subgroup.mem_map.mpr ⟨τ, ?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
      show (N : ℤ) ∣ τ.1 1 0
      simpa [τ] using hN_q
    · rw [← hσ_eq]
      apply Units.ext
      ext i j
      rw [diagConj_entry k hk]
      have hq_q : ((σ.1 1 0 : ℤ) : ℚ) = (k : ℚ) * ((q : ℤ) : ℚ) := by exact_mod_cast hq
      have h_τ_val : ∀ a b, ((mapGL ℚ τ).val a b : ℚ) =
          ((τ.val a b : ℤ) : ℚ) := by
        intros; simp [mapGL_coe_matrix, Matrix.map_apply, algebraMap_int_eq]
      have h_σ_val : ∀ a b, ((mapGL ℚ σ).val a b : ℚ) =
          ((σ.val a b : ℤ) : ℚ) := by
        intros; simp [mapGL_coe_matrix, Matrix.map_apply, algebraMap_int_eq]
      simp only [h_τ_val, h_σ_val]
      have h_inv : (↑k : ℚ)⁻¹ = 1 / (↑k : ℚ) := by rw [one_div]
      have h_div : ((σ.val 1 0 : ℤ) : ℚ) / (k : ℚ) = (q : ℚ) := by
        rw [hq_q]; field_simp
      fin_cases i <;> fin_cases j <;> simp [τ]
      · exact h_div.symm

set_option maxHeartbeats 6400000 in
/-- **Gamma0 degree multiplicativity**: `deg(diag(1,m)) * deg(diag(1,n)) = deg(diag(1,mn))`
when `gcd(m,n) = 1`, where all degrees are at the Gamma0(N) level.

Mathematically: `[Γ₀(N) : Γ₀(Nm)] * [Γ₀(N) : Γ₀(Nn)] = [Γ₀(N) : Γ₀(Nmn)]`.
This follows from the tower formula plus the product property
`Γ₀(Nm) · Γ₀(Nn) = Γ₀(N)`, which holds because for coprime `m, n`,
the conditions `Nm | σ₁₀` and `Nn | σ₁₀` on different prime factors
are independently satisfiable via lower-unipotent coset representatives.

**Proof**: Two-step CRT decomposition.
1. `Γ₀(mN) · Γ(N) = Γ₀(N)`: the image of `Γ₀(mN)` in `Γ₀(N)/Γ(N) ≅ B(ℤ/Nℤ)` is
   the full upper-triangular group (by lifting via `SL₂(ℤ) → SL₂(ℤ/Nℤ)` surjectivity,
   then adjusting the lower-left entry mod `m` using `gcd(d,b) = 1` from `det = 1`).
2. `Γ(mN) · Γ(nN) = Γ(N)`: from `Gamma_gcd_eq_mul` since `gcd(mN,nN) = N·gcd(m,n) = N`.

Combining: any `γ ∈ Γ₀(N)` writes as `γ = σ·δ` with `σ ∈ Γ₀(mN), δ ∈ Γ(N)`, then
`δ = α·β` with `α ∈ Γ(mN) ⊂ Γ₀(mN), β ∈ Γ(nN) ⊂ Γ₀(nN)`, giving
`γ = (σα)·β ∈ Γ₀(mN)·Γ₀(nN)`.

With `Γ₀(mN) ∩ Γ₀(nN) = Γ₀(mnN)` (from `lcm(mN,nN) = mnN` when `gcd(m,n)=1`),
the CRT map `Γ₀(N)/Γ₀(mnN) → Γ₀(N)/Γ₀(mN) × Γ₀(N)/Γ₀(nN)` is a bijection. -/
lemma Gamma0_deg_coprime_mul (N : ℕ) [NeZero N]
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n) (hcop : Nat.Coprime m n) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, m]) (fun i => by fin_cases i <;> simp [hm_pos])
        (by simp [Int.gcd_one_left])) *
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, n]) (fun i => by fin_cases i <;> simp [hn_pos])
        (by simp [Int.gcd_one_left])) =
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, m * n])
        (fun i => by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
        (by simp [Int.gcd_one_left])) := by
  set g_m : (Gamma0_pair N).Δ := ⟨diagMat 2 (![1, m]),
    diagMat_mem_Delta0_of_gcd N _ (fun i => by fin_cases i <;> simp [hm_pos]) (by simp)⟩
  set g_n : (Gamma0_pair N).Δ := ⟨diagMat 2 (![1, n]),
    diagMat_mem_Delta0_of_gcd N _ (fun i => by fin_cases i <;> simp [hn_pos]) (by simp)⟩
  set g_mn : (Gamma0_pair N).Δ := ⟨diagMat 2 (![1, m * n]),
    diagMat_mem_Delta0_of_gcd N _ (fun i => by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
      (by simp)⟩
  change HeckeRing.HeckeCoset_deg _ ⟦g_m⟧ * HeckeRing.HeckeCoset_deg _ ⟦g_n⟧ =
    HeckeRing.HeckeCoset_deg _ ⟦g_mn⟧
  have h_rep_card : ∀ (g : (Gamma0_pair N).Δ),
      Nat.card (HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep ⟦g⟧)) =
      Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g) := by
    intro g
    have h_mk := HeckeCoset.mk_rep (⟦g⟧ : HeckeRing.HeckeCoset (Gamma0_pair N))
    rw [HeckeCoset.eq_iff] at h_mk
    have h_in : (HeckeCoset.rep ⟦g⟧ : GL (Fin 2) ℚ) ∈
        DoubleCoset.doubleCoset (g : GL (Fin 2) ℚ)
          ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
      rw [← h_mk]; exact DoubleCoset.mem_doubleCoset_self _ _ _
    rw [DoubleCoset.mem_doubleCoset] at h_in
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, h_eq⟩ := h_in
    let g_mid : (Gamma0_pair N).Δ := ⟨γ₁ * ↑g * γ₂, h_eq ▸ (HeckeCoset.rep ⟦g⟧).2⟩
    have h_mid : (g_mid : GL (Fin 2) ℚ) = HeckeCoset.rep ⟦g⟧ := h_eq.symm
    exact Nat.card_congr (
      (Equiv.cast (congrArg (HeckeRing.decompQuot (Gamma0_pair N))
        (Subtype.ext h_mid))).symm.trans
      (HeckeRing.decompQuot_double_H_equiv (Gamma0_pair N) g ⟨γ₁, hγ₁⟩ ⟨γ₂, hγ₂⟩
        (h_eq ▸ (HeckeCoset.rep ⟦g⟧).2)))
  simp only [HeckeRing.HeckeCoset_deg]
  haveI : Fintype (HeckeRing.decompQuot (Gamma0_pair N) g_m) :=
    HeckeRing.instFintypeDecompQuot _ _
  haveI : Fintype (HeckeRing.decompQuot (Gamma0_pair N) g_n) :=
    HeckeRing.instFintypeDecompQuot _ _
  haveI : Fintype (HeckeRing.decompQuot (Gamma0_pair N) g_mn) :=
    HeckeRing.instFintypeDecompQuot _ _
  rw [show (Fintype.card (HeckeRing.decompQuot (Gamma0_pair N)
        (HeckeCoset.rep ⟦g_m⟧)) : ℤ) =
      Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_m) from by
      rw [← Nat.card_eq_fintype_card, h_rep_card],
    show (Fintype.card (HeckeRing.decompQuot (Gamma0_pair N)
        (HeckeCoset.rep ⟦g_n⟧)) : ℤ) =
      Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_n) from by
      rw [← Nat.card_eq_fintype_card, h_rep_card],
    show (Fintype.card (HeckeRing.decompQuot (Gamma0_pair N)
        (HeckeCoset.rep ⟦g_mn⟧)) : ℤ) =
      Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_mn) from by
      rw [← Nat.card_eq_fintype_card, h_rep_card]]
  set H := (Gamma0_pair N).H
  set K_m := ((CongruenceSubgroup.Gamma0 (m * N)).map (mapGL ℚ)).subgroupOf H
  set K_n := ((CongruenceSubgroup.Gamma0 (n * N)).map (mapGL ℚ)).subgroupOf H
  set K_mn := ((CongruenceSubgroup.Gamma0 (m * n * N)).map (mapGL ℚ)).subgroupOf H
  have h_stab_m := stab_diag_eq_Gamma0 N m hm_pos
  have h_stab_n := stab_diag_eq_Gamma0 N n hn_pos
  have h_stab_mn := stab_diag_eq_Gamma0 N (m * n) (Nat.mul_pos hm_pos hn_pos)
  rw [show Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_m) = Nat.card (↥H ⧸ K_m) from
      Nat.card_congr (Subgroup.quotientEquivOfEq h_stab_m),
    show Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_n) = Nat.card (↥H ⧸ K_n) from
      Nat.card_congr (Subgroup.quotientEquivOfEq h_stab_n),
    show Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_mn) = Nat.card (↥H ⧸ K_mn) from
      Nat.card_congr (Subgroup.quotientEquivOfEq h_stab_mn)]
  have h_inf : K_m ⊓ K_n = K_mn := by
    simp only [K_m, K_n, K_mn, Subgroup.subgroupOf, ← Subgroup.comap_inf]
    congr 1
    rw [← Subgroup.map_inf_eq (f := mapGL ℚ) (hf := mapGL_injective)]
    congr 1
    have hN_pos : 0 < N := Nat.pos_of_neZero N
    haveI : NeZero (m * N) := ⟨by positivity⟩
    haveI : NeZero (n * N) := ⟨by positivity⟩
    haveI : NeZero (m * n * N) := ⟨by positivity⟩
    exact Gamma0_inf_eq_of_coprime N m n hcop
  haveI hf_m : Fintype (HeckeRing.decompQuot (Gamma0_pair N) g_m) :=
    HeckeRing.instFintypeDecompQuot _ _
  haveI hf_n : Fintype (HeckeRing.decompQuot (Gamma0_pair N) g_n) :=
    HeckeRing.instFintypeDecompQuot _ _
  haveI hf_mn : Fintype (HeckeRing.decompQuot (Gamma0_pair N) g_mn) :=
    HeckeRing.instFintypeDecompQuot _ _
  haveI : Finite (HeckeRing.decompQuot (Gamma0_pair N) g_m) := @Fintype.finite _ hf_m
  haveI : Finite (HeckeRing.decompQuot (Gamma0_pair N) g_n) := @Fintype.finite _ hf_n
  haveI : Finite (HeckeRing.decompQuot (Gamma0_pair N) g_mn) := @Fintype.finite _ hf_mn
  haveI : Finite (↥H ⧸ K_m) :=
    Finite.of_equiv _ (Subgroup.quotientEquivOfEq h_stab_m)
  haveI : Finite (↥H ⧸ K_n) :=
    Finite.of_equiv _ (Subgroup.quotientEquivOfEq h_stab_n)
  haveI : Finite (↥H ⧸ K_mn) :=
    Finite.of_equiv _ (Subgroup.quotientEquivOfEq h_stab_mn)
  haveI : K_m.FiniteIndex := ⟨by rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne'⟩
  haveI : K_n.FiniteIndex := ⟨by rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne'⟩
  haveI : (K_m ⊓ K_n).FiniteIndex := by
    rw [h_inf]; exact ⟨by rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne'⟩
  rw [← h_inf]
  push_cast
  symm
  exact_mod_cast card_quotient_inf_of_set_mul K_m K_n (by
    intro ⟨g, hg⟩
    obtain ⟨γ, hγ_mem, hγ_eq⟩ := Subgroup.mem_map.mp hg
    have hN_pos : 0 < N := Nat.pos_of_neZero N
    haveI : NeZero (m * N) := ⟨by positivity⟩
    haveI : NeZero (n * N) := ⟨by positivity⟩
    obtain ⟨σ_m, hσ_m, hδ_m⟩ := Gamma0_mN_mul_GammaN_eq_Gamma0 N m hm_pos γ hγ_mem
    set δ := σ_m⁻¹ * γ with hδ_def
    have h_gcd : Nat.gcd (m * N) (n * N) = N := by
      rw [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]
    have hδ_mem : δ ∈ CongruenceSubgroup.Gamma N := hδ_m
    have hδ_sup : δ ∈ CongruenceSubgroup.Gamma (m * N) ⊔
        CongruenceSubgroup.Gamma (n * N) := by
      haveI : NeZero ((m * N).gcd (n * N)) := ⟨by rw [h_gcd]; exact hN_pos.ne'⟩
      have h_eq := Gamma_gcd_eq_mul (m * N) (n * N)
      rw [← Subgroup.map_sup, h_gcd] at h_eq
      exact Subgroup.map_injective mapGL_injective h_eq ▸ (h_gcd ▸ hδ_mem)
    haveI : (CongruenceSubgroup.Gamma (n * N)).Normal := CongruenceSubgroup.Gamma_normal _
    obtain ⟨α, hα, β, hβ, hαβ⟩ := Subgroup.mem_sup_of_normal_right.mp hδ_sup
    have hα_Gamma0 : α ∈ CongruenceSubgroup.Gamma0 (m * N) :=
      GammaN_le_Gamma0 (m * N) hα
    have hβ_Gamma0 : β ∈ CongruenceSubgroup.Gamma0 (n * N) :=
      GammaN_le_Gamma0 (n * N) hβ
    have Gamma0_antitone : ∀ (a b : ℕ), a ∣ b →
        CongruenceSubgroup.Gamma0 b ≤ CongruenceSubgroup.Gamma0 a := by
      intro a b hab η hη
      rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hη ⊢
      exact dvd_trans (Int.natCast_dvd_natCast.mpr hab) hη
    have h_factor : γ = σ_m * α * β := by
      rw [mul_assoc, hαβ, hδ_def, ← mul_assoc, mul_inv_cancel, one_mul]
    refine ⟨⟨mapGL ℚ (σ_m * α), ?_⟩, ?_, ⟨mapGL ℚ β, ?_⟩, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem _ (Gamma0_antitone N (m * N)
        (Nat.dvd_mul_left N m) (Subgroup.mul_mem _ hσ_m hα_Gamma0))
    · rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mul_mem _ hσ_m hα_Gamma0)
    · exact Subgroup.mem_map_of_mem _ (Gamma0_antitone N (n * N)
        (Nat.dvd_mul_left N n) hβ_Gamma0)
    · rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem _ hβ_Gamma0
    · -- Goal: g = (mapGL ℚ) (σ_m * α) * (mapGL ℚ) β as elements of H.
      apply Subtype.ext
      show g = ((mapGL ℚ) (σ_m * α)) * ((mapGL ℚ) β)
      rw [← hγ_eq, h_factor]
      simp only [map_mul, mul_assoc])

/-- **Helper: ConjAct-smul by an element of H preserves H.**
Inlined from the private `conjAct_smul_eq_of_mem` in `GLn/Degree.lean`. -/
private lemma conjAct_smul_H_eq_of_mem_local {G : Type*} [Group G] (H : Subgroup G)
    {h : G} (hh : h ∈ H) : ConjAct.toConjAct h • H = H := by
  ext x; constructor
  · intro hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have h_eq : ConjAct.toConjAct h • ((ConjAct.toConjAct h)⁻¹ • x) = x := smul_inv_smul _ x
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at h_eq
    rw [← h_eq]; exact H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
  · intro hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (ConjAct.toConjAct h)⁻¹ • x = h⁻¹ * x * h := by
      show ConjAct.ofConjAct (ConjAct.toConjAct h)⁻¹ * x *
        (ConjAct.ofConjAct (ConjAct.toConjAct h)⁻¹)⁻¹ = _
      simp [ConjAct.ofConjAct_toConjAct, mul_assoc]
    rw [this]; exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh

/-- **Bridge: `deg_{Γ₀(N)}(T'(1, k)) = [Γ₀(N) : Γ₀(kN)]`**.
The Gamma0 Hecke degree of the diagonal coset `diag(1, k)` equals the relative index
of `Γ₀(kN)` in `Γ₀(N)`. Proof: the representative `δ` of `T_diag_Gamma0 N ![1,k]` lies
in the double coset of `diag(1,k)`, so writing `δ = σ₁ · diag(1,k) · σ₂` with
`σ₁, σ₂ ∈ H = Γ₀(N).map(mapGL)`, conjugation by `σ₁, σ₂ ∈ H` preserves `H`, so
`(ConjAct δ • H).relIndex H = (ConjAct diag(1,k) • H).relIndex H`. Then
`stab_diag_eq_Gamma0` identifies the stabiliser on `H` with `Γ₀(kN).map(mapGL).subgroupOf H`,
which via `mapGL` injectivity gives `Γ₀(kN).relIndex Γ₀(N)`. -/
private lemma HeckeCoset_deg_Gamma0_one_k_eq_relIndex (N : ℕ) [NeZero N]
    (k : ℕ) (hk : 0 < k) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, k]) (fun i => by fin_cases i <;> simp [hk])
        (by simp [Int.gcd_one_left])) =
    ((CongruenceSubgroup.Gamma0 (k * N)).relIndex (CongruenceSubgroup.Gamma0 N) : ℤ) := by
  set D := T_diag_Gamma0 N (![1, k]) (fun i => by fin_cases i <;> simp [hk])
    (by simp [Int.gcd_one_left]) with hD_def
  set δ := HeckeCoset.rep D
  set α := (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ)
  set H := (Gamma0_pair N).H
  have hδ_mem : (δ : GL (Fin 2) ℚ) ∈ DoubleCoset.doubleCoset α (H : Set _) (H : Set _) := by
    have h1 : HeckeCoset.toSet D =
        DoubleCoset.doubleCoset α (H : Set _) (H : Set _) := by
      simp only [D, T_diag_Gamma0, HeckeCoset.toSet_mk]; rfl
    rw [← h1]; exact HeckeCoset.rep_mem D
  rw [DoubleCoset.mem_doubleCoset] at hδ_mem
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hδ_eq⟩ := hδ_mem
  have h_smul_σ₁ : ConjAct.toConjAct σ₁ • H = H := conjAct_smul_H_eq_of_mem_local H hσ₁
  have h_smul_σ₂ : ConjAct.toConjAct σ₂ • H = H := conjAct_smul_H_eq_of_mem_local H hσ₂
  have h_δ_smul : ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H =
      ConjAct.toConjAct σ₁ • (ConjAct.toConjAct α • H) := by
    rw [hδ_eq, map_mul, map_mul, ← smul_smul, ← smul_smul, h_smul_σ₂]
  have h_S1 : (ConjAct.toConjAct α • H).relIndex H =
      (ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H).relIndex H := by
    rw [h_δ_smul]
    have := Subgroup.relIndex_pointwise_smul
      (ConjAct.toConjAct σ₁) (ConjAct.toConjAct α • H) H
    rw [h_smul_σ₁] at this; exact this.symm
  have h_def : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D =
      ↑((ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H).relIndex H) := by
    simp only [HeckeRing.HeckeCoset_deg, Subgroup.relIndex, Subgroup.index,
      ← Nat.card_eq_fintype_card]; rfl
  have h_stab := stab_diag_eq_Gamma0 N k hk
  have h_relIndex_stab : (ConjAct.toConjAct α • H).relIndex H =
      ((CongruenceSubgroup.Gamma0 (k * N)).map (mapGL ℚ)).relIndex H := by
    unfold Subgroup.relIndex; rw [h_stab]
  rw [h_def, ← h_S1, h_relIndex_stab]
  have h_map_relIndex : ((CongruenceSubgroup.Gamma0 (k * N)).map (mapGL ℚ)).relIndex
      ((CongruenceSubgroup.Gamma0 N).map (mapGL ℚ)) =
      (CongruenceSubgroup.Gamma0 (k * N)).relIndex (CongruenceSubgroup.Gamma0 N) :=
    Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective
  show ((((CongruenceSubgroup.Gamma0 (k * N)).map (mapGL ℚ)).relIndex H : ℕ) : ℤ) =
      ((CongruenceSubgroup.Gamma0 (k * N)).relIndex (CongruenceSubgroup.Gamma0 N) : ℤ)
  rw [← h_map_relIndex]; rfl

/-- **T1-A: Gamma0 relative index = Gamma0 index for coprime case**.
For `m, N` coprime (both positive, `N` nonzero), the relative index of `Γ₀(mN)` in `Γ₀(N)`
equals the absolute index of `Γ₀(m)` in `SL₂(ℤ)`:
`[Γ₀(N) : Γ₀(mN)] = [SL₂(ℤ) : Γ₀(m)]`.

**Proof**: Apply `Gamma0_deg_coprime_mul` with `N(arg) := 1`, `m(arg) := m`, `n(arg) := N`
(using `[NeZero 1]`) to get the SL₂-level multiplicativity:
`[SL₂ : Γ₀(m)] · [SL₂ : Γ₀(N)] = [SL₂ : Γ₀(m·N)]`.
Tower formula: `[SL₂ : Γ₀(m·N)] = [Γ₀(N) : Γ₀(m·N)] · [SL₂ : Γ₀(N)]`.
Cancel `[SL₂ : Γ₀(N)]` (finite, positive) to get the result. -/
private lemma Gamma0_relIndex_eq_Gamma_index_of_coprime (N : ℕ) [NeZero N]
    (m : ℕ) (hm_pos : 0 < m) (hcop : Nat.Coprime m N) :
    (CongruenceSubgroup.Gamma0 (m * N)).relIndex (CongruenceSubgroup.Gamma0 N) =
    (CongruenceSubgroup.Gamma0 m).index := by
  have hN_pos : 0 < N := Nat.pos_of_neZero N
  have h_deg_level1 := Gamma0_deg_coprime_mul 1 m N hm_pos hN_pos hcop
  have h_bridge_m := HeckeCoset_deg_Gamma0_one_k_eq_relIndex 1 m hm_pos
  have h_bridge_N := HeckeCoset_deg_Gamma0_one_k_eq_relIndex 1 N hN_pos
  have h_bridge_mN := HeckeCoset_deg_Gamma0_one_k_eq_relIndex 1 (m * N)
    (Nat.mul_pos hm_pos hN_pos)
  have hGamma0_one : CongruenceSubgroup.Gamma0 1 = (⊤ : Subgroup SL(2, ℤ)) := by
    ext g
    simp only [CongruenceSubgroup.Gamma0_mem, Subgroup.mem_top, iff_true]
    exact Subsingleton.elim _ _
  have h_relIndex_to_index : ∀ (k : ℕ),
      (CongruenceSubgroup.Gamma0 (k * 1)).relIndex (CongruenceSubgroup.Gamma0 1) =
      (CongruenceSubgroup.Gamma0 k).index := by
    intro k
    rw [Nat.mul_one, hGamma0_one, Subgroup.relIndex_top_right]
  rw [h_relIndex_to_index m] at h_bridge_m
  rw [h_relIndex_to_index N] at h_bridge_N
  rw [h_relIndex_to_index (m * N)] at h_bridge_mN
  rw [h_bridge_m, h_bridge_N, h_bridge_mN] at h_deg_level1
  have hle : CongruenceSubgroup.Gamma0 (m * N) ≤ CongruenceSubgroup.Gamma0 N := by
    intro g hg; rw [CongruenceSubgroup.Gamma0_mem] at hg ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hg ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_mul_left N m)) hg
  have h_tower : (CongruenceSubgroup.Gamma0 (m * N)).relIndex (CongruenceSubgroup.Gamma0 N) *
      (CongruenceSubgroup.Gamma0 N).index = (CongruenceSubgroup.Gamma0 (m * N)).index :=
    Subgroup.relIndex_mul_index hle
  haveI : (CongruenceSubgroup.Gamma0 N).FiniteIndex := inferInstance
  have hN_index_ne : (CongruenceSubgroup.Gamma0 N).index ≠ 0 :=
    Subgroup.FiniteIndex.index_ne_zero
  have h_mul_cancel : (CongruenceSubgroup.Gamma0 (m * N)).relIndex (CongruenceSubgroup.Gamma0 N) *
      (CongruenceSubgroup.Gamma0 N).index =
      (CongruenceSubgroup.Gamma0 m).index * (CongruenceSubgroup.Gamma0 N).index := by
    rw [h_tower]; exact_mod_cast h_deg_level1.symm
  exact (mul_right_cancel_iff_of_pos (Nat.pos_of_ne_zero hN_index_ne)).mp h_mul_cancel

/-- **T1-B1: Degree formula for `T'(1, p^k)` at `Γ₀(N)` level**.
For prime `p` coprime to `N`, `k ≥ 1`:
`deg_{Γ₀(N)}(T'(1, p^k)) = p^(k-1) · (p + 1)`.

**Proof**: By the bridge `HeckeCoset_deg_Gamma0_one_k_eq_relIndex`, this equals
`[Γ₀(N) : Γ₀(p^k · N)]`. By T1-A `Gamma0_relIndex_eq_Gamma_index_of_coprime`
(using `Nat.Coprime.pow_left`), this equals `(Gamma0 (p^k)).index`. By
`HeckeRing.GL2.Gamma0_prime_power_index`, this equals `p^(k-1) · (p + 1)`. -/
lemma HeckeCoset_deg_Gamma0_one_ppow (N : ℕ) [NeZero N]
    (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N) (k : ℕ) (hk : 0 < k) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, p^k])
        (fun i => by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp [Int.gcd_one_left])) =
    ((p ^ (k - 1) * (p + 1) : ℕ) : ℤ) := by
  have h_bridge := HeckeCoset_deg_Gamma0_one_k_eq_relIndex N (p^k) (pow_pos hp.pos k)
  rw [h_bridge]
  have hpkN_cop : Nat.Coprime (p^k) N := hpN.pow_left k
  have hpk_pos : 0 < p^k := pow_pos hp.pos k
  have h_T1A := Gamma0_relIndex_eq_Gamma_index_of_coprime N (p^k) hpk_pos hpkN_cop
  rw [h_T1A]
  rw [HeckeRing.GL2.Gamma0_prime_power_index p hp k hk]

/-- **T1-B2: Degree formula for `T'(p, p^k)` at `Γ₀(N)` level**.
For prime `p` coprime to `N`, `k ≥ 1`:
- `deg_{Γ₀(N)}(T'(p, p)) = 1` (scalar case, k=1)
- `deg_{Γ₀(N)}(T'(p, p^k)) = p^(k-2) · (p + 1)` for k ≥ 2

**Proof**: Use scalar centrality. `diag(p, p^k) = diag(p,p) · diag(1, p^(k-1))`.
Scalar element `diag(p,p)` centralizes GL₂(ℚ), so the stabilizer of `diag(p, p^k)` equals
the stabilizer of `diag(1, p^(k-1))`. Then apply T1-B1 (HeckeCoset_deg_Gamma0_one_ppow)
for k-1 ≥ 1, or the scalar case for k=1. -/
lemma HeckeCoset_deg_Gamma0_p_ppow (N : ℕ) [NeZero N]
    (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N) (k : ℕ) (hk : 1 ≤ k) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![p, p^k])
        (fun i => by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
        (by show Int.gcd (↑p) ↑N = 1
            rw [Int.gcd_natCast_natCast]; exact hpN)) =
    (if k = 1 then (1 : ℤ) else ((p^(k-2) * (p + 1) : ℕ) : ℤ)) := by
  set D := T_diag_Gamma0 N (![p, p^k])
    (fun i => by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
    (by show Int.gcd (↑p) ↑N = 1; rw [Int.gcd_natCast_natCast]; exact hpN)
  set δ := (HeckeCoset.rep D : GL (Fin 2) ℚ) with hδ_def
  set α : GL (Fin 2) ℚ := diagMat 2 (![p, p^k] : Fin 2 → ℕ)
  set α_sc : GL (Fin 2) ℚ := diagMat 2 (fun _ : Fin 2 => p)
  set α_diag : GL (Fin 2) ℚ := diagMat 2 (![1, p^(k-1)] : Fin 2 → ℕ)
  set H := (Gamma0_pair N).H
  have hα_pos : ∀ i : Fin 2, 0 < (![p, p^k] : Fin 2 → ℕ) i := fun i => by
    fin_cases i <;> simp [hp.pos, pow_pos hp.pos]
  have hδ_mem : δ ∈ DoubleCoset.doubleCoset α (↑H : Set _) (↑H : Set _) := by
    have h_set : HeckeCoset.toSet D = DoubleCoset.doubleCoset α (↑H : Set _) (↑H : Set _) := by
      simp only [D, T_diag_Gamma0, HeckeCoset.toSet_mk, α]; rfl
    rw [← h_set]; exact HeckeCoset.rep_mem D
  rw [DoubleCoset.mem_doubleCoset] at hδ_mem
  obtain ⟨h₁, hh₁, h₂, hh₂, hδ_eq⟩ := hδ_mem
  -- Step 2: diag(p, p^k) = diag(p,p) * diag(1, p^(k-1))
  have hα_factor : α = α_sc * α_diag := by
    apply Units.ext
    simp only [α, α_sc, α_diag, Units.val_mul]
    rw [diagMat_val 2 (![p, p^k] : Fin 2 → ℕ) hα_pos,
        diagMat_val 2 (fun _ : Fin 2 => p) (fun _ => hp.pos),
        diagMat_val 2 (![1, p^(k-1)] : Fin 2 → ℕ) (fun i => by
          fin_cases i <;> simp [pow_pos hp.pos])]
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
    have hpk : (p : ℚ) ^ k = (p : ℚ) * (p : ℚ) ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    fin_cases i <;> fin_cases j <;> push_cast <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hpk,
        show (1 : Fin 2) ≠ 0 from by decide]
  -- Step 3: conjAct(α) • H = conjAct(α_diag) • H (by scalar centrality)
  have h_conjAct_sc : ConjAct.toConjAct α_sc • H = H := by
    show ConjAct.toConjAct (diagMat 2 (fun _ : Fin 2 => p) : GL (Fin 2) ℚ) • H = H
    ext x; constructor
    · intro hx; rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
      simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hx
      rwa [diagMat_scalar_conj_eq 2 p hp.pos] at hx
    · intro hx; rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
      rwa [diagMat_scalar_conj_eq 2 p hp.pos]
  have h_conj_eq : ConjAct.toConjAct α • H = ConjAct.toConjAct α_diag • H := by
    rw [hα_factor, map_mul, ← smul_smul]
    conv_lhs => rw [show ConjAct.toConjAct α_sc • (ConjAct.toConjAct α_diag • H) =
                     (ConjAct.toConjAct α_sc • ConjAct.toConjAct α_diag • H) from rfl]
    -- Use Subgroup.relIndex_pointwise_smul or direct: conjAct α_sc • X = X when α_sc central
    -- Actually: (conjAct α_sc) • (conjAct α_diag • H) = conjAct α_diag • H? No.
    -- We need: ∀ X ⊂ GL, (conjAct α_sc) • X = X when α_sc is central.
    -- This holds because conjAct(central) = identity (since p * g * p⁻¹ = g).
    have h_sc_central : ∀ (X : Subgroup (GL (Fin 2) ℚ)),
        ConjAct.toConjAct α_sc • X = X := by
      intro X
      ext x; constructor
      · intro hx
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
        simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hx
        rwa [diagMat_scalar_conj_eq 2 p hp.pos] at hx
      · intro hx
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
        rwa [diagMat_scalar_conj_eq 2 p hp.pos]
    exact h_sc_central _
  -- Step 4: relIndex chain
  have h_def : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D =
      ↑((ConjAct.toConjAct δ • H).relIndex H) := by
    simp only [HeckeRing.HeckeCoset_deg, Subgroup.relIndex, Subgroup.index,
      ← Nat.card_eq_fintype_card]; rfl
  have h_smul_h₁ : ConjAct.toConjAct h₁ • H = H := conjAct_smul_elt_eq H ⟨h₁, hh₁⟩
  have h_smul_h₂ : ConjAct.toConjAct h₂ • H = H := conjAct_smul_elt_eq H ⟨h₂, hh₂⟩
  have h_δ_smul : ConjAct.toConjAct δ • H =
      ConjAct.toConjAct h₁ • (ConjAct.toConjAct α • H) := by
    rw [hδ_eq, map_mul, map_mul, ← smul_smul, ← smul_smul, h_smul_h₂]
  have h_relIndex_δ : (ConjAct.toConjAct δ • H).relIndex H =
      (ConjAct.toConjAct α • H).relIndex H := by
    rw [h_δ_smul]
    have := Subgroup.relIndex_pointwise_smul
      (ConjAct.toConjAct h₁) (ConjAct.toConjAct α • H) H
    rw [h_smul_h₁] at this; exact this
  rw [h_def, h_relIndex_δ, h_conj_eq]
  by_cases hk1 : k = 1
  · subst hk1
    rw [if_pos rfl]
    have h_α_diag_one : α_diag = (1 : GL (Fin 2) ℚ) := by
      simp only [α_diag, show (1 : ℕ) - 1 = 0 from rfl, pow_zero]
      apply Units.ext
      ext i j
      rw [diagMat_val 2 (![1, 1] : Fin 2 → ℕ) (fun i => by fin_cases i <;> simp),
          Units.val_one]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.cons_val_zero,
              Matrix.cons_val_one, Matrix.head_cons]
    rw [h_α_diag_one]
    simp only [ConjAct.toConjAct_one, one_smul]
    rw [Subgroup.relIndex_self]; simp
  · rw [if_neg hk1]
    have hk_ge : 2 ≤ k := by omega
    have hk1_pos : 0 < k - 1 := by omega
    have h_pos : ∀ i : Fin 2, 0 < (![1, p^(k-1)] : Fin 2 → ℕ) i := fun i => by
      fin_cases i <;> simp [pow_pos hp.pos]
    have h_gcd : Int.gcd ((![1, p^(k-1)] : Fin 2 → ℕ) 0 : ℤ) ↑N = 1 := by simp
    have h_T1B1 := HeckeCoset_deg_Gamma0_one_ppow N p hp hpN (k - 1) hk1_pos
    set D' := T_diag_Gamma0 N (![1, p ^ (k-1)])
      (fun i => by fin_cases i <;> simp [pow_pos hp.pos])
      (by simp [Int.gcd_one_left])
    have h_def' : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D' =
        ↑((ConjAct.toConjAct (HeckeCoset.rep D' : GL (Fin 2) ℚ) • H).relIndex H) := by
      simp only [HeckeRing.HeckeCoset_deg, Subgroup.relIndex, Subgroup.index,
        ← Nat.card_eq_fintype_card]; rfl
    -- rep D' is in DC(α_diag), so ConjAct(rep D') • H has same relIndex as ConjAct(α_diag) • H
    have hδ'_mem : (HeckeCoset.rep D' : GL (Fin 2) ℚ) ∈
        DoubleCoset.doubleCoset α_diag (↑H : Set _) (↑H : Set _) := by
      have h_set : HeckeCoset.toSet D' = DoubleCoset.doubleCoset α_diag (↑H : Set _) (↑H : Set _) := by
        simp only [D', T_diag_Gamma0, HeckeCoset.toSet_mk, α_diag]; rfl
      rw [← h_set]; exact HeckeCoset.rep_mem D'
    rw [DoubleCoset.mem_doubleCoset] at hδ'_mem
    obtain ⟨h₁', hh₁', h₂', hh₂', hδ'_eq⟩ := hδ'_mem
    have h_smul_h₁' : ConjAct.toConjAct h₁' • H = H := conjAct_smul_elt_eq H ⟨h₁', hh₁'⟩
    have h_smul_h₂' : ConjAct.toConjAct h₂' • H = H := conjAct_smul_elt_eq H ⟨h₂', hh₂'⟩
    have h_δ'_smul : ConjAct.toConjAct (HeckeCoset.rep D' : GL (Fin 2) ℚ) • H =
        ConjAct.toConjAct h₁' • (ConjAct.toConjAct α_diag • H) := by
      rw [hδ'_eq, map_mul, map_mul, ← smul_smul, ← smul_smul, h_smul_h₂']
    have h_relIndex_δ' : (ConjAct.toConjAct (HeckeCoset.rep D' : GL (Fin 2) ℚ) • H).relIndex H =
        (ConjAct.toConjAct α_diag • H).relIndex H := by
      rw [h_δ'_smul]
      have := Subgroup.relIndex_pointwise_smul
        (ConjAct.toConjAct h₁') (ConjAct.toConjAct α_diag • H) H
      rw [h_smul_h₁'] at this; exact this
    rw [← h_relIndex_δ', ← h_def', h_T1B1]
    have : k - 1 - 1 = k - 2 := by omega
    rw [this]


end HeckeRing.GLn
