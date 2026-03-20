/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.PrimeDecomposition

/-!
# GL₂ Hecke Algebra: Definitions for Theorem 3.24

Specialization of the GL_n Hecke algebra to n=2. Defines T(a,d), T(m), and
structural lemmas for Shimura's Theorem 3.24.

## Main definitions

* `T_ad` -- `T(a,d)` basis element
* `T_pp` -- scalar double coset `T(p,p)`
* `T_sum` -- Shimura's `T(m) = Σ T(a,d)` over divisor pairs

## References

* Shimura, Theorem 3.24
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset HeckeRing.GLn

open scoped Pointwise

namespace HeckeRing.GL2

/-- `T(a,d)` for n=2: the Hecke basis element for diagonal `(a,d)` with `a | d`.
    Returns 0 when `a = 0` or `d = 0` or `a ∤ d`. -/
noncomputable def T_ad (a d : ℕ) : HeckeAlgebra 2 :=
  if h : 0 < a ∧ 0 < d ∧ a ∣ d then
    T_elem 2 ![a, d] (fun i => by fin_cases i <;> simp [*])
      (fun i hi => by (have : i = 0 := by omega); subst this; simpa using h.2.2)
  else 0

/-- Unfold `T_ad` when positivity and divisibility hold. -/
lemma T_ad_of_pos (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (h : a ∣ d) :
    T_ad a d = T_elem 2 ![a, d]
      (fun i => by fin_cases i <;> simp [*])
      (fun i hi => by (have : i = 0 := by omega); subst this; simpa using h) := by
  simp [T_ad, ha, hd, h]

/-- `T_ad` returns 0 when the conditions fail. -/
lemma T_ad_eq_zero {a d : ℕ} (h : ¬(0 < a ∧ 0 < d ∧ a ∣ d)) :
    T_ad a d = 0 := by
  simp [T_ad, h]

/-- `T(p,p)` -- the scalar double coset. -/
noncomputable def T_pp (p : ℕ) : HeckeAlgebra 2 := T_ad p p

/-- Hecke operator `T⦃a, d⦄`. -/
scoped notation "T⦃" a ", " d "⦄" => T_ad a d

/-- Diamond operator `◇n = T(n,n)`. -/
scoped prefix:max "◇" => T_pp

/-- Integer diagonal matrix `Diag(a, d)` for 2×2. -/
scoped notation "Diag(" a ", " d ")" =>
  Matrix.diagonal (![a, d] : Fin 2 → ℤ)

/-- Unfold `T_pp` when `p` is prime. -/
lemma T_pp_of_pos (p : ℕ) (hp : p.Prime) :
    T_pp p = T_elem 2 (fun _ => p) (fun _ => hp.pos)
      (divChain_const 2 p) := by
  simp only [T_pp, T_ad_of_pos p p hp.pos hp.pos (dvd_refl _)]
  exact T_elem_congr_diag 2 (funext fun i => by fin_cases i <;> rfl)
    (fun i => by fin_cases i <;> simp [hp.pos]) (fun _ => hp.pos)
    (fun i hi => by (have : i = 0 := by omega); subst this; simp)
    (divChain_const 2 p)

lemma T_pp_eq_T_ad (p : ℕ) : ◇ p = T⦃p, p⦄ := rfl

lemma T_elem_ones_eq :
    T_elem 2 (fun _ => 1) (fun _ => Nat.one_pos)
      (divChain_const 2 1) = 1 := by
  show T_single (GL_pair 2) ℤ
    (T_diag 2 (fun _ => 1) (fun _ => Nat.one_pos)
      (divChain_const 2 1)) 1 = 1
  rw [T_diag_ones 2]
  exact (one_eq_T_single (GL_pair 2)).symm

/-- T(1,1) is the identity element. -/
lemma T_ad_one_one : T⦃1, 1⦄ = 1 := by
  rw [T_ad_of_pos 1 1 Nat.one_pos Nat.one_pos (dvd_refl _)]
  have heq : (![1, 1] : Fin 2 → ℕ) = fun _ => 1 :=
    funext fun i => by fin_cases i <;> rfl
  exact (T_elem_congr_diag 2 heq
    (fun i => by fin_cases i <;> exact Nat.one_pos) (fun _ => Nat.one_pos)
    (fun i hi => by (have : i = 0 := by omega); subst this; simp)
    (divChain_const 2 1)).trans T_elem_ones_eq

/-- Deprecated alias for `T_ad`. -/
noncomputable abbrev T_ad' := @T_ad

/-- `T(m) = Σ_{a | m} T(a, m/a)`. -/
noncomputable def T_sum (m : ℕ+) : HeckeAlgebra 2 :=
  ∑ a ∈ (m : ℕ).divisors, T_ad a ((m : ℕ) / a)

section Structural

variable (p : ℕ) (hp : p.Prime)

private lemma doubleCoset_eq_of_mem' (g δ : GL (Fin 2) ℚ)
    (h : g ∈ DoubleCoset.doubleCoset δ (SLnZ_subgroup 2) (SLnZ_subgroup 2)) :
    DoubleCoset.doubleCoset g (SLnZ_subgroup 2) (SLnZ_subgroup 2) =
    DoubleCoset.doubleCoset δ (SLnZ_subgroup 2) (SLnZ_subgroup 2) := by
  rw [DoubleCoset.mem_doubleCoset] at h
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := h
  rw [heq]
  exact (DoubleCoset.doubleCoset_mul_right_eq_self (GL_pair 2) ⟨h₂, hh₂⟩ (h₁ * δ)).trans
    (doset_mul_left_eq_self (GL_pair 2) ⟨h₁, hh₁⟩ δ)

/-- For p prime, T(p) = T_ad(1,p). -/
lemma T_sum_prime :
    T_sum ⟨p, hp.pos⟩ = T⦃1, p⦄ := by
  show ∑ a ∈ p.divisors, T_ad' a (p / a) = _
  rw [hp.sum_divisors, Nat.div_self hp.pos, Nat.div_one]
  have h1 : T_ad' p 1 = 0 := by
    apply T_ad_eq_zero
    push_neg
    intro _ _
    exact fun hdvd => hp.one_lt.not_ge (Nat.le_of_dvd Nat.one_pos hdvd)
  have h2 : T_ad' 1 p = T_ad 1 p := rfl
  rw [h1, h2, zero_add]

private lemma diagMul_scalar_comm (b : Fin 2 → ℕ) (c : ℕ) :
    b * (fun _ => c) = (fun _ => c) * b := by
  ext i; exact Nat.mul_comm _ _

private lemma T_diag_choose_mem_doubleCoset [NeZero n]
    (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hdiv : DivChain n a) :
    ((T_diag n a ha hdiv).eql.choose : GL (Fin n) ℚ) ∈
    DoubleCoset.doubleCoset (diagMat n a ha : GL (Fin n) ℚ)
      (GL_pair n).H (GL_pair n).H := by
  have h_spec := (T_diag n a ha hdiv).eql.choose_spec
  simp only [T_diag, T_mk, diagMat_delta] at h_spec
  rw [h_spec]; exact DoubleCoset.mem_doubleCoset_self _ _ _

private lemma scalar_product_mem_doubleCoset
    (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c)
    (x1 db x2 dc : GL (Fin 2) ℚ)
    (h₁b : GL (Fin 2) ℚ) (hh₁b : h₁b ∈ (GL_pair 2).H)
    (h₂b : GL (Fin 2) ℚ) (hh₂b : h₂b ∈ (GL_pair 2).H)
    (h₁c : GL (Fin 2) ℚ) (hh₁c : h₁c ∈ (GL_pair 2).H)
    (h₂c : GL (Fin 2) ℚ) (hh₂c : h₂c ∈ (GL_pair 2).H)
    (hx1 : x1 ∈ (GL_pair 2).H) (hx2 : x2 ∈ (GL_pair 2).H)
    (hδb_eq : db = h₁b * diagMat 2 b hb_pos * h₂b)
    (hδc_eq : dc = h₁c * diagMat 2 (fun _ => c) (fun _ => hc) * h₂c) :
    x1 * db * (x2 * dc) ∈
    DoubleCoset.doubleCoset
      (diagMat 2 (b * (fun _ => c))
        (pi_mul_pos 2 b _ hb_pos (fun _ => hc)) :
        GL (Fin 2) ℚ) (GL_pair 2).H (GL_pair 2).H := by
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨x1 * h₁b, (GL_pair 2).H.mul_mem hx1 hh₁b,
          h₂b * x2 * h₁c * h₂c,
          (GL_pair 2).H.mul_mem ((GL_pair 2).H.mul_mem
            ((GL_pair 2).H.mul_mem hh₂b hx2) hh₁c) hh₂c, ?_⟩
  rw [hδb_eq, hδc_eq]
  have h_comm := diagMat_scalar_comm 2 c hc (h₂b * x2 * h₁c)
  calc x1 * (h₁b * diagMat 2 b hb_pos * h₂b) *
      (x2 * (h₁c * diagMat 2 (fun _ => c) (fun _ => hc) * h₂c))
      = x1 * h₁b * (diagMat 2 b hb_pos * (h₂b * x2 * h₁c)) *
        (diagMat 2 (fun _ => c) (fun _ => hc) * h₂c) := by group
    _ = x1 * h₁b * (diagMat 2 b hb_pos *
          (diagMat 2 (fun _ => c) (fun _ => hc) *
            (h₂b * x2 * h₁c))) * h₂c := by
        have : (h₂b * x2 * h₁c) * diagMat 2 (fun _ => c) (fun _ => hc) =
            diagMat 2 (fun _ => c) (fun _ => hc) * (h₂b * x2 * h₁c) :=
          h_comm.symm
        calc x1 * h₁b * (diagMat 2 b hb_pos * (h₂b * x2 * h₁c)) *
            (diagMat 2 (fun _ => c) (fun _ => hc) * h₂c)
            = x1 * h₁b * (diagMat 2 b hb_pos *
                ((h₂b * x2 * h₁c) *
                  diagMat 2 (fun _ => c) (fun _ => hc))) * h₂c := by group
          _ = x1 * h₁b * (diagMat 2 b hb_pos *
                (diagMat 2 (fun _ => c) (fun _ => hc) *
                  (h₂b * x2 * h₁c))) * h₂c := by rw [this]
    _ = x1 * h₁b *
        (diagMat 2 (b * (fun _ => c))
          (pi_mul_pos 2 b _ hb_pos (fun _ => hc)) *
          (h₂b * x2 * h₁c)) * h₂c := by
        rw [show diagMat 2 b hb_pos *
            (diagMat 2 (fun _ => c) (fun _ => hc) *
              (h₂b * x2 * h₁c)) =
            (diagMat 2 b hb_pos *
              diagMat 2 (fun _ => c) (fun _ => hc)) *
              (h₂b * x2 * h₁c) from by group,
          diagMat_mul]
    _ = x1 * h₁b *
        diagMat 2 (b * (fun _ => c))
          (pi_mul_pos 2 b _ hb_pos (fun _ => hc)) *
        (h₂b * x2 * h₁c * h₂c) := by group

private lemma mulMap_right_scalar_eq (b : Fin 2 → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb : DivChain 2 b)
    (c : ℕ) (hc : 0 < c)
    (hbc : DivChain 2 (b * (fun _ => c)))
    (p : decompQuot (GL_pair 2) (T_diag 2 b hb_pos hb) ×
         decompQuot (GL_pair 2)
           (T_diag 2 (fun _ => c) (fun _ => hc)
             (divChain_const 2 c))) :
    mulMap (GL_pair 2) (T_diag 2 b hb_pos hb)
      (T_diag 2 (fun _ => c) (fun _ => hc)
        (divChain_const 2 c)) p =
    T_diag 2 (b * (fun _ => c))
      (pi_mul_pos 2 b _ hb_pos (fun _ => hc)) hbc := by
  set H := (GL_pair 2).H
  have hδb := T_diag_choose_mem_doubleCoset (n := 2) b hb_pos hb
  rw [DoubleCoset.mem_doubleCoset] at hδb
  obtain ⟨h₁b, hh₁b, h₂b, hh₂b, hδb_eq⟩ := hδb
  have hδc := T_diag_choose_mem_doubleCoset (n := 2)
    (fun _ => c) (fun _ => hc) (divChain_const 2 c)
  rw [DoubleCoset.mem_doubleCoset] at hδc
  obtain ⟨h₁c, hh₁c, h₂c, hh₂c, hδc_eq⟩ := hδc
  apply HeckeRing.T'_ext (GL_pair 2)
  exact doubleCoset_eq_of_mem' _ _
    (scalar_product_mem_doubleCoset b hb_pos hb c hc
      p.1.out _ p.2.out _ h₁b hh₁b h₂b hh₂b
      h₁c hh₁c h₂c hh₂c
      (SetLike.coe_mem _) (SetLike.coe_mem _)
      hδb_eq hδc_eq)

/-- When D_c is a scalar coset, its representative normalizes H, so coset
    representatives for D_b that map to the same product coset must be equal. -/
private lemma scalar_coset_rep_normalizes (c : ℕ) (hc : 0 < c) :
    let D_c := T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)
    let H' := (GL_pair 2).H
    let δ_c := (D_c.eql.choose : GL (Fin 2) ℚ)
    ({δ_c} : Set (GL (Fin 2) ℚ)) * (H' : Set (GL (Fin 2) ℚ)) =
    (H' : Set (GL (Fin 2) ℚ)) * {δ_c} := by
  intro D_c H' δ_c
  have hδc_mem : δ_c ∈
      DoubleCoset.doubleCoset (diagMat 2 (fun _ => c) (fun _ => hc) : GL (Fin 2) ℚ)
        H' H' := by
    have h_spec := D_c.eql.choose_spec
    simp only [D_c, T_diag, T_mk, diagMat_delta] at h_spec
    rw [h_spec]; exact DoubleCoset.mem_doubleCoset_self H' H' _
  rw [DoubleCoset.mem_doubleCoset] at hδc_mem
  obtain ⟨h₁c, hh₁c, h₂c, hh₂c, hδc_eq⟩ := hδc_mem
  have hδc_simp : δ_c = (h₁c * h₂c) * diagMat 2 (fun _ => c) (fun _ => hc) := by
    rw [hδc_eq, mul_assoc, diagMat_scalar_comm 2 c hc h₂c, ← mul_assoc]
  have hδc_norm : ConjAct.toConjAct δ_c • H' = H' := by
    rw [hδc_simp, map_mul, ← smul_smul, conjAct_scalar_smul_eq]
    exact HeckeRing.conjAct_smul_elt_eq H' ⟨h₁c * h₂c, H'.mul_mem hh₁c hh₂c⟩
  have h_norm_coe : ({δ_c} : Set (GL (Fin 2) ℚ)) * (H' : Set (GL (Fin 2) ℚ)) * {δ_c⁻¹} =
      (H' : Set (GL (Fin 2) ℚ)) := by
    have h1 : (ConjAct.toConjAct δ_c • H' : Set (GL (Fin 2) ℚ)) =
        (H' : Set (GL (Fin 2) ℚ)) := by
      rw [show (ConjAct.toConjAct δ_c • H' : Set (GL (Fin 2) ℚ)) =
          ((ConjAct.toConjAct δ_c • H' : Subgroup _) : Set (GL (Fin 2) ℚ)) by rfl]
      congr 1
    rw [conjAct_smul_coe_eq] at h1
    exact h1
  have := congrFun (congrArg HMul.hMul h_norm_coe) {δ_c}
  simp_rw [mul_assoc, Set.singleton_mul_singleton] at this
  simpa using this

/-- D_bc is in the mulSupport of D_b * D_c when D_c is scalar. -/
private lemma mem_mulSupport_right_scalar (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c) (hbc : DivChain 2 (b * (fun _ => c))) :
    let D_b := T_diag 2 b hb_pos hb
    let D_c := T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)
    let D_bc := T_diag 2 (b * (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc)) hbc
    D_bc ∈ HeckeRing.mulSupport (GL_pair 2) D_b D_c := by
  intro D_b D_c D_bc
  simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
    true_and, Prod.exists]
  have ⟨i₀⟩ : Nonempty (decompQuot (GL_pair 2) D_b) :=
    Fintype.card_pos_iff.mp (by
      have := HeckeRing.T'_deg_pos (GL_pair 2) D_b
      simp only [HeckeRing.T'_deg] at this; omega)
  have h_card : Fintype.card (decompQuot (GL_pair 2) D_c) = 1 := by
    have := T'_deg_scalar 2 c hc
    simp only [HeckeRing.T'_deg] at this; exact_mod_cast this
  have ⟨j₀⟩ : Nonempty (decompQuot (GL_pair 2) D_c) :=
    Fintype.card_pos_iff.mp (by rw [h_card]; exact Nat.one_pos)
  exact ⟨i₀, j₀, mulMap_right_scalar_eq b hb_pos hb c hc hbc (i₀, j₀)⟩

private lemma m'_right_scalar_eq_one (b : Fin 2 → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb : DivChain 2 b)
    (c : ℕ) (hc : 0 < c)
    (hbc : DivChain 2 (b * (fun _ => c)))
    (D_b : T' (GL_pair 2)) (hDb : D_b = T_diag 2 b hb_pos hb)
    (D_c : T' (GL_pair 2))
    (hDc : D_c = T_diag 2 (fun _ => c) (fun _ => hc)
      (divChain_const 2 c))
    (D_bc : T' (GL_pair 2))
    (hDbc : D_bc = T_diag 2 (b * (fun _ => c))
      (diagMul_pos 2 b _ hb_pos (fun _ => hc)) hbc) :
    HeckeRing.m' (GL_pair 2) D_b D_c D_bc = 1 := by
  have h_card : Fintype.card (decompQuot (GL_pair 2)
      (T_diag 2 (fun _ => c) (fun _ => hc)
        (divChain_const 2 c))) = 1 := by
    have := T'_deg_scalar 2 c hc
    simp only [HeckeRing.T'_deg] at this; exact_mod_cast this
  haveI : Subsingleton (decompQuot (GL_pair 2)
      (T_diag 2 (fun _ => c) (fun _ => hc)
        (divChain_const 2 c))) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_card)
  have h_le : HeckeRing.m' (GL_pair 2) (T_diag 2 b hb_pos hb)
      (T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c))
      (T_diag 2 (b * (fun _ => c))
        (diagMul_pos 2 b _ hb_pos (fun _ => hc)) hbc) ≤ 1 := by
    classical
    simp only [HeckeRing.m']; norm_cast; rw [Nat.card_eq_fintype_card]
    apply Fintype.card_le_one_iff_subsingleton.mpr
    constructor; intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
    have hj : j₁ = j₂ := Subsingleton.elim j₁ j₂; subst hj
    simp only [Set.mem_setOf_eq] at h₁ h₂
    have hi : i₁ = i₂ := by
      by_contra hne
      apply HeckeRing.decompQuot_coset_diff (GL_pair 2) (T_diag 2 b hb_pos hb) i₁ i₂ hne
      have hδc_comm_H := scalar_coset_rep_normalizes c hc
      have hτ_mem : (j₁.out : GL (Fin 2) ℚ) ∈ (GL_pair 2).H :=
        SetLike.coe_mem j₁.out
      let δ_c := ((T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)).eql.choose :
                   GL (Fin 2) ℚ)
      have h_coset :
          ({(j₁.out : GL (Fin 2) ℚ) * δ_c} : Set _) *
            ((GL_pair 2).H : Set _) =
          ((GL_pair 2).H : Set _) * {δ_c} := by
        rw [← Set.singleton_mul_singleton, mul_assoc,
          hδc_comm_H, ← mul_assoc,
          Subgroup.singleton_mul_subgroup hτ_mem]
      have h12' :
          ({(i₁.out : GL (Fin 2) ℚ) * (T_diag 2 b hb_pos hb).eql.choose} :
            Set _) * (((GL_pair 2).H : Set _) * {δ_c}) =
          ({(i₂.out : GL (Fin 2) ℚ) * (T_diag 2 b hb_pos hb).eql.choose} :
            Set _) * (((GL_pair 2).H : Set _) * {δ_c}) := by
        have lhs_eq :
            ({(i₁.out : GL (Fin 2) ℚ) * (T_diag 2 b hb_pos hb).eql.choose} :
              Set _) *
            {(j₁.out : GL (Fin 2) ℚ) * δ_c} *
            ((GL_pair 2).H : Set _) =
            ({(i₁.out : GL (Fin 2) ℚ) * (T_diag 2 b hb_pos hb).eql.choose} :
              Set _) *
              (((GL_pair 2).H : Set _) * {δ_c}) := by
          rw [mul_assoc, h_coset]
        have rhs_eq :
            ({(i₂.out : GL (Fin 2) ℚ) * (T_diag 2 b hb_pos hb).eql.choose} :
              Set _) *
            {(j₁.out : GL (Fin 2) ℚ) * δ_c} *
            ((GL_pair 2).H : Set _) =
            ({(i₂.out : GL (Fin 2) ℚ) * (T_diag 2 b hb_pos hb).eql.choose} :
              Set _) *
              (((GL_pair 2).H : Set _) * {δ_c}) := by
          rw [mul_assoc, h_coset]
        rw [← lhs_eq, ← rhs_eq]
        exact h₁.trans h₂.symm
      rw [← mul_assoc, ← mul_assoc] at h12'
      exact HeckeRing.mul_singleton_right_cancel δ_c _ _ h12'
    subst hi; rfl
  have h_pos : 0 < HeckeRing.m' (GL_pair 2) (T_diag 2 b hb_pos hb)
      (T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c))
      (T_diag 2 (b * (fun _ => c))
        (diagMul_pos 2 b _ hb_pos (fun _ => hc)) hbc) := by
    have h_mem := mem_mulSupport_right_scalar b hb_pos hb c hc hbc
    simp only at h_mem
    have h_ne := HeckeRing.m'_pos_of_mem_mulSupport (GL_pair 2) (T_diag 2 b hb_pos hb)
      (T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c))
      (T_diag 2 (b * (fun _ => c))
        (diagMul_pos 2 b _ hb_pos (fun _ => hc)) hbc) h_mem
    have : (0 : ℤ) ≤ HeckeRing.m' (GL_pair 2) (T_diag 2 b hb_pos hb)
      (T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c))
      (T_diag 2 (b * (fun _ => c))
        (diagMul_pos 2 b _ hb_pos (fun _ => hc)) hbc) := by
      simp only [HeckeRing.m']; exact Nat.cast_nonneg _
    omega
  -- Now rewrite back to abstract D_b, D_c, D_bc using the equality hypotheses
  rw [← hDb, ← hDc, ← hDbc] at h_le h_pos
  omega

private lemma m'_right_scalar_eq_zero (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c) (hbc : DivChain 2 (b * (fun _ => c)))
    (A : T' (GL_pair 2)) (hA : A ≠ T_diag 2 (b * (fun _ => c))
      (diagMul_pos 2 b _ hb_pos (fun _ => hc)) hbc) :
    HeckeRing.m' (GL_pair 2)
      (T_diag 2 b hb_pos hb)
      (T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)) A = 0 := by
  apply HeckeRing.m'_eq_zero_of_nmem_mulSupport
  intro h_mem
  simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
    true_and] at h_mem
  obtain ⟨⟨i, j⟩, heq⟩ := h_mem
  exact hA (heq.symm.trans (mulMap_right_scalar_eq b hb_pos hb c hc hbc (i, j)))

/-- Right scalar multiplication: `T_elem(b) * T_elem(c,...,c) = T_elem(b*c)`. -/
theorem T_elem_mul_scalar (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c) :
    T_elem 2 b hb_pos hb * T_elem 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c) =
    T_elem 2 (b * (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc))
      (DivChain_mul 2 b (fun _ => c) hb (divChain_const 2 c)) := by
  set D_b := T_diag 2 b hb_pos hb
  set D_c := T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)
  set D_bc := T_diag 2 (b * (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc))
    (DivChain_mul 2 b (fun _ => c) hb (divChain_const 2 c))
  change HeckeRing.T_single (GL_pair 2) ℤ D_b 1 *
    HeckeRing.T_single (GL_pair 2) ℤ D_c 1 =
    HeckeRing.T_single (GL_pair 2) ℤ D_bc 1
  rw [HeckeRing.T_single_one_mul_T_single_one]
  apply Finsupp.ext; intro A
  simp only [HeckeRing.m, Finsupp.coe_mk, HeckeRing.T_single]
  by_cases h1 : A = D_bc
  · subst h1
    norm_num [Finsupp.single_apply]
    exact m'_right_scalar_eq_one b hb_pos hb c hc
      (DivChain_mul 2 b (fun _ => c) hb (divChain_const 2 c))
      D_b rfl D_c rfl D_bc rfl
  · norm_num [Finsupp.single_apply, h1]
    exact m'_right_scalar_eq_zero b hb_pos hb c hc
      (DivChain_mul 2 b (fun _ => c) hb (divChain_const 2 c)) A h1

/-- T(p,p) commutes with every T_elem. -/
lemma T_pp_comm_T_elem (p : ℕ) (hp : p.Prime)
    (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i)
    (ha : DivChain 2 a) :
    ◇ p * T_elem 2 a ha_pos ha = T_elem 2 a ha_pos ha * ◇ p := by
  rw [T_pp_of_pos p hp]
  rw [T_diag_scalar_mul 2 p hp.pos a ha_pos ha, T_elem_mul_scalar a ha_pos ha p hp.pos]
  exact (T_elem_congr_diag 2 (diagMul_scalar_comm a p)
    (diagMul_pos 2 a _ ha_pos (fun _ => hp.pos))
    (diagMul_pos 2 _ a (fun _ => hp.pos) ha_pos)
    (DivChain_mul 2 a _ ha (divChain_const 2 p))
    (DivChain_mul 2 _ _ (divChain_const 2 p) ha)).symm

/-- Powers of T(p,p): `T(p,p)^i = T(p^i, p^i)`. -/
lemma T_pp_pow (i : ℕ) :
    ◇ p ^ i =
    T_elem 2 (fun _ => p ^ i) (fun _ => pow_pos hp.pos i) (divChain_const 2 _) := by
  induction i with
  | zero =>
    simp only [pow_zero]
    symm
    have heq : (fun (_ : Fin 2) => p ^ 0) = fun _ => 1 :=
      funext fun _ => by simp
    exact (T_elem_congr_diag 2 heq (fun _ => pow_pos hp.pos 0) (fun _ => Nat.one_pos)
      (divChain_const 2 _) (divChain_const 2 1)).trans T_elem_ones_eq
  | succ i ih =>
    rw [pow_succ', ih]
    rw [T_pp_of_pos p hp]
    rw [T_diag_scalar_mul 2 p hp.pos (fun _ => p ^ i) (fun _ => pow_pos hp.pos i)
      (divChain_const 2 _)]
    exact T_elem_congr_diag 2
      (funext fun _ => by simp [Pi.mul_apply, pow_succ, mul_comm])
      (diagMul_pos 2 _ _ (fun _ => hp.pos) (fun _ => pow_pos hp.pos i))
      (fun _ => pow_pos hp.pos (i + 1))
      (DivChain_mul 2 _ _ (divChain_const 2 p) (divChain_const 2 _))
      (divChain_const 2 _)

/-- The divisor pairs of p^k with a|d are (p^i, p^(k-i)) for i <= k/2. -/
lemma T_sum_ppow_expansion (k : ℕ) :
    T_sum ⟨p ^ k, pow_pos hp.pos k⟩ =
    ∑ i ∈ Finset.range (k / 2 + 1),
      T_ad' (p ^ i) (p ^ (k - i)) := by
  show ∑ a ∈ (p ^ k).divisors, T_ad' a (p ^ k / a) = _
  rw [Nat.sum_divisors_prime_pow hp]
  have h_div : ∀ j ∈ Finset.range (k + 1),
      T_ad' (p ^ j) (p ^ k / p ^ j) = T_ad' (p ^ j) (p ^ (k - j)) := by
    intro j hj; rw [Finset.mem_range] at hj; congr 1; exact Nat.pow_div (by omega) hp.pos
  rw [Finset.sum_congr rfl h_div]
  exact (Finset.sum_subset (Finset.range_mono (by omega)) (fun j hj hnj => by
    simp only [Finset.mem_range] at hj hnj
    apply T_ad_eq_zero
    push_neg
    intro _ _
    exact fun hdvd => absurd (Nat.le_of_dvd (pow_pos hp.pos _) hdvd)
      (not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt (by omega))))).symm

end Structural

end HeckeRing.GL2
