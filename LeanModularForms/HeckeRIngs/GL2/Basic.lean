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

/-- `T(a,d)` for n=2: the Hecke basis element for diagonal `(a,d)` with `a | d`. -/
noncomputable def T_ad (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (h : a ∣ d) :
    HeckeAlgebra 2 :=
  T_elem 2 ![a, d] (fun i => by fin_cases i <;> simp [*])
    (fun i hi => by (have : i = 0 := by omega); subst this; simpa using h)

/-- `T(p,p)` -- the scalar double coset. -/
noncomputable def T_pp (p : ℕ) (hp : p.Prime) : HeckeAlgebra 2 :=
  T_elem 2 (fun _ => p) (fun _ => hp.pos) (divChain_const 2 p)

lemma T_pp_eq_T_ad (p : ℕ) (hp : p.Prime) :
    T_pp p hp = T_ad p p hp.pos hp.pos (dvd_refl _) := by
  unfold T_pp T_ad
  exact T_elem_congr_diag 2 (funext fun i => by fin_cases i <;> rfl)
    (fun _ => hp.pos) (fun i => by fin_cases i <;> simp [hp.pos])
    (divChain_const 2 p)
    (fun i hi => by (have : i = 0 := by omega); subst this; simp)

lemma T_elem_ones_eq :
    T_elem 2 (fun _ => 1) (fun _ => Nat.one_pos) (divChain_const 2 1) = 1 := by
  show T_single (GL_pair 2) ℤ
    (T_diag 2 (fun _ => 1) (fun _ => Nat.one_pos) (divChain_const 2 1)) 1 = 1
  rw [T_diag_ones 2]
  exact (one_eq_T_single (GL_pair 2)).symm

/-- T(1,1) is the identity element. -/
lemma T_ad_one_one : T_ad 1 1 Nat.one_pos Nat.one_pos (dvd_refl _) = 1 := by
  unfold T_ad
  have heq : (![1, 1] : Fin 2 → ℕ) = fun _ => 1 := funext fun i => by fin_cases i <;> rfl
  have h := T_elem_congr_diag 2 heq
    (fun i => by fin_cases i <;> exact Nat.one_pos) (fun _ => Nat.one_pos)
    (fun i hi => by (have : i = 0 := by omega); subst this; simp)
    (divChain_const 2 1)
  rw [h]
  exact T_elem_ones_eq

noncomputable def T_ad' (a d : ℕ) : HeckeAlgebra 2 :=
  if h : 0 < a ∧ 0 < d ∧ a ∣ d then
    T_ad a d h.1 h.2.1 h.2.2
  else 0

/-- `T(m) = Σ_{a | m} T_ad'(a, m/a)`. -/
noncomputable def T_sum (m : ℕ+) : HeckeAlgebra 2 :=
  ∑ a ∈ (m : ℕ).divisors, T_ad' a ((m : ℕ) / a)

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
    T_sum ⟨p, hp.pos⟩ = T_ad 1 p Nat.one_pos hp.pos (one_dvd _) := by
  show ∑ a ∈ p.divisors, T_ad' a (p / a) = _
  rw [hp.sum_divisors, Nat.div_self hp.pos, Nat.div_one]
  have h1 : T_ad' p 1 = 0 := by
    unfold T_ad'
    rw [dif_neg]
    push_neg
    intro _ _
    exact fun hdvd => hp.one_lt.not_ge (Nat.le_of_dvd Nat.one_pos hdvd)
  have h2 : T_ad' 1 p = T_ad 1 p Nat.one_pos hp.pos (one_dvd _) := by
    unfold T_ad'
    rw [dif_pos ⟨Nat.one_pos, hp.pos, one_dvd p⟩]
  rw [h1, h2, zero_add]

private lemma diagMul_scalar_comm (b : Fin 2 → ℕ) (c : ℕ) :
    diagMul 2 b (fun _ => c) = diagMul 2 (fun _ => c) b := by
  ext i; exact Nat.mul_comm _ _

private lemma mulMap_right_scalar_eq (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c) (hbc : DivChain 2 (diagMul 2 b (fun _ => c)))
    (p : decompQuot (GL_pair 2) (T_diag 2 b hb_pos hb) ×
         decompQuot (GL_pair 2) (T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c))) :
    mulMap (GL_pair 2) (T_diag 2 b hb_pos hb)
      (T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)) p =
    T_diag 2 (diagMul 2 b (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc)) hbc := by
  set H := (GL_pair 2).H
  have hδb_mem : ((T_diag 2 b hb_pos hb).eql.choose : GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (diagMat 2 b hb_pos : GL (Fin 2) ℚ) H H := by
    have h_spec := (T_diag 2 b hb_pos hb).eql.choose_spec
    simp only [T_diag, T_mk, diagMat_delta] at h_spec
    rw [h_spec]; exact DoubleCoset.mem_doubleCoset_self H H _
  rw [DoubleCoset.mem_doubleCoset] at hδb_mem
  obtain ⟨h₁b, hh₁b, h₂b, hh₂b, hδb_eq⟩ := hδb_mem
  have hδc_mem : ((T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)).eql.choose :
      GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (diagMat 2 (fun _ => c) (fun _ => hc) : GL (Fin 2) ℚ) H H := by
    have h_spec := (T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)).eql.choose_spec
    simp only [T_diag, T_mk, diagMat_delta] at h_spec
    rw [h_spec]; exact DoubleCoset.mem_doubleCoset_self H H _
  rw [DoubleCoset.mem_doubleCoset] at hδc_mem
  obtain ⟨h₁c, hh₁c, h₂c, hh₂c, hδc_eq⟩ := hδc_mem
  have h_product_mem : (p.1.out : GL (Fin 2) ℚ) *
      ((T_diag 2 b hb_pos hb).eql.choose : GL (Fin 2) ℚ) *
      ((p.2.out : GL (Fin 2) ℚ) *
        ((T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)).eql.choose :
          GL (Fin 2) ℚ)) ∈
      DoubleCoset.doubleCoset
        (diagMat 2 (diagMul 2 b (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc)) :
          GL (Fin 2) ℚ) H H := by
    rw [DoubleCoset.mem_doubleCoset]
    set x1 := (↑(Quotient.out p.1) : GL (Fin 2) ℚ)
    set db := ((T_diag 2 b hb_pos hb).eql.choose : GL (Fin 2) ℚ)
    set x2 := (↑(Quotient.out p.2) : GL (Fin 2) ℚ)
    set dc := ((T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)).eql.choose :
      GL (Fin 2) ℚ)
    refine ⟨(p.1.out : GL (Fin 2) ℚ) * h₁b,
            H.mul_mem (SetLike.coe_mem p.1.out) hh₁b,
            h₂b * p.2.out * h₁c * h₂c,
            H.mul_mem (H.mul_mem (H.mul_mem hh₂b (SetLike.coe_mem p.2.out)) hh₁c) hh₂c,
            ?_⟩
    rw [show db = h₁b * diagMat 2 b hb_pos * h₂b from hδb_eq,
        show dc = h₁c * diagMat 2 (fun _ => c) (fun _ => hc) * h₂c from hδc_eq]
    have h_comm : diagMat 2 (fun _ => c) (fun _ => hc) * (h₂b * x2 * h₁c) =
        (h₂b * x2 * h₁c) * diagMat 2 (fun _ => c) (fun _ => hc) :=
      diagMat_scalar_comm 2 c hc (h₂b * x2 * h₁c)
    have key : x1 * (h₁b * diagMat 2 b hb_pos * h₂b) *
        (x2 * (h₁c * diagMat 2 (fun _ => c) (fun _ => hc) * h₂c)) =
        x1 * h₁b *
          (diagMat 2 (diagMul 2 b (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc)) *
            (h₂b * x2 * h₁c)) *
        h₂c := by
      calc x1 * (h₁b * diagMat 2 b hb_pos * h₂b) *
          (x2 * (h₁c * diagMat 2 (fun _ => c) (fun _ => hc) * h₂c))
          = x1 * h₁b * (diagMat 2 b hb_pos * (h₂b * x2 * h₁c)) *
            (diagMat 2 (fun _ => c) (fun _ => hc) * h₂c) := by group
        _ = x1 * h₁b *
            (diagMat 2 b hb_pos *
              ((h₂b * x2 * h₁c) * diagMat 2 (fun _ => c) (fun _ => hc))) *
            h₂c := by group
        _ = x1 * h₁b *
            (diagMat 2 b hb_pos *
              (diagMat 2 (fun _ => c) (fun _ => hc) * (h₂b * x2 * h₁c))) *
            h₂c := by rw [h_comm.symm]
        _ = x1 * h₁b *
            ((diagMat 2 b hb_pos * diagMat 2 (fun _ => c) (fun _ => hc)) *
              (h₂b * x2 * h₁c)) *
            h₂c := by group
        _ = x1 * h₁b *
            (diagMat 2 (diagMul 2 b (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc)) *
              (h₂b * x2 * h₁c)) *
            h₂c := by rw [diagMat_mul]
    calc x1 * (h₁b * diagMat 2 b hb_pos * h₂b) *
        (x2 * (h₁c * diagMat 2 (fun _ => c) (fun _ => hc) * h₂c))
        = x1 * h₁b *
          (diagMat 2 (diagMul 2 b (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc)) *
            (h₂b * x2 * h₁c)) *
          h₂c := key
      _ = x1 * h₁b *
          diagMat 2 (diagMul 2 b (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc)) *
            (h₂b * x2 * h₁c * h₂c) := by group
  apply HeckeRing.T'_ext (GL_pair 2)
  exact doubleCoset_eq_of_mem' _ _ h_product_mem

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

set_option maxHeartbeats 16000000 in
private lemma decompQuot_eq_of_scalar_fiber (b : Fin 2 → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb : DivChain 2 b)
    (c : ℕ) (hc : 0 < c)
    (i₁ i₂ : decompQuot (GL_pair 2) (T_diag 2 b hb_pos hb))
    (j₁ : decompQuot (GL_pair 2)
      (T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)))
    (h_eq :
      mulMap (GL_pair 2) (T_diag 2 b hb_pos hb)
        (T_diag 2 (fun _ => c) (fun _ => hc)
          (divChain_const 2 c)) (i₁, j₁) =
      mulMap (GL_pair 2) (T_diag 2 b hb_pos hb)
        (T_diag 2 (fun _ => c) (fun _ => hc)
          (divChain_const 2 c)) (i₂, j₁)) :
    i₁ = i₂ := by
  by_contra hne
  apply HeckeRing.decompQuot_coset_diff (GL_pair 2)
    (T_diag 2 b hb_pos hb) i₁ i₂ hne
  have h_eq' : ({(i₁.out : GL (Fin 2) ℚ) *
      (T_diag 2 b hb_pos hb).eql.choose} : Set _) *
    {(j₁.out : GL (Fin 2) ℚ) *
      (T_diag 2 (fun _ => c) (fun _ => hc)
        (divChain_const 2 c)).eql.choose} *
    ((GL_pair 2).H : Set _) =
    ({(i₂.out : GL (Fin 2) ℚ) *
      (T_diag 2 b hb_pos hb).eql.choose} : Set _) *
    {(j₁.out : GL (Fin 2) ℚ) *
      (T_diag 2 (fun _ => c) (fun _ => hc)
        (divChain_const 2 c)).eql.choose} *
    ((GL_pair 2).H : Set _) := by
    have := congr_arg T'.set h_eq; simp [mulMap] at this; exact this
  set δ_c := (T_diag 2 (fun _ => c) (fun _ => hc)
    (divChain_const 2 c)).eql.choose
  set H' := (GL_pair 2).H
  have hδc_comm_H := scalar_coset_rep_normalizes c hc
  have hτ_mem : (j₁.out : GL (Fin 2) ℚ) ∈ H' :=
    SetLike.coe_mem j₁.out
  have h_coset :
      ({(j₁.out : GL (Fin 2) ℚ) * δ_c} : Set _) *
        (H' : Set _) =
      (H' : Set _) * {δ_c} := by
    rw [← Set.singleton_mul_singleton, mul_assoc,
      hδc_comm_H, ← mul_assoc,
      Subgroup.singleton_mul_subgroup hτ_mem]
  have h12' :
      ({(i₁.out : GL (Fin 2) ℚ) * D_b.eql.choose} :
        Set _) * ((H' : Set _) * {δ_c}) =
      ({(i₂.out : GL (Fin 2) ℚ) * D_b.eql.choose} :
        Set _) * ((H' : Set _) * {δ_c}) := by
    have lhs_eq :
        ({(i₁.out : GL (Fin 2) ℚ) * D_b.eql.choose} :
          Set _) *
        {(j₁.out : GL (Fin 2) ℚ) * δ_c} *
        (H' : Set _) =
        ({(i₁.out : GL (Fin 2) ℚ) * D_b.eql.choose} :
          Set _) * ((H' : Set _) * {δ_c}) := by
      rw [mul_assoc, h_coset]
    have rhs_eq :
        ({(i₂.out : GL (Fin 2) ℚ) * D_b.eql.choose} :
          Set _) *
        {(j₁.out : GL (Fin 2) ℚ) * δ_c} *
        (H' : Set _) =
        ({(i₂.out : GL (Fin 2) ℚ) * D_b.eql.choose} :
          Set _) * ((H' : Set _) * {δ_c}) := by
      rw [mul_assoc, h_coset]
    rw [← lhs_eq, ← rhs_eq]; exact h_eq
  rw [← mul_assoc, ← mul_assoc] at h12'
  exact HeckeRing.mul_singleton_right_cancel δ_c _ _ h12'

/-- D_bc is in the mulSupport of D_b * D_c when D_c is scalar. -/
private lemma mem_mulSupport_right_scalar (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c) (hbc : DivChain 2 (diagMul 2 b (fun _ => c))) :
    let D_b := T_diag 2 b hb_pos hb
    let D_c := T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)
    let D_bc := T_diag 2 (diagMul 2 b (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc)) hbc
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

private lemma m'_right_scalar_eq_one (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c) (hbc : DivChain 2 (diagMul 2 b (fun _ => c))) :
    HeckeRing.m' (GL_pair 2)
      (T_diag 2 b hb_pos hb)
      (T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c))
      (T_diag 2 (diagMul 2 b (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc)) hbc) = 1 := by
  set D_b := T_diag 2 b hb_pos hb
  set D_c := T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)
  set D_bc := T_diag 2 (diagMul 2 b (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc)) hbc
  have h_card : Fintype.card (decompQuot (GL_pair 2) D_c) = 1 := by
    have := T'_deg_scalar 2 c hc
    simp only [HeckeRing.T'_deg] at this; exact_mod_cast this
  haveI : Subsingleton (decompQuot (GL_pair 2) D_c) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_card)
  have h_le : HeckeRing.m' (GL_pair 2) D_b D_c D_bc ≤ 1 := by
    classical
    simp only [HeckeRing.m']; norm_cast; rw [Nat.card_eq_fintype_card]
    apply Fintype.card_le_one_iff_subsingleton.mpr
    constructor; intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
    have hj : j₁ = j₂ := Subsingleton.elim j₁ j₂; subst hj
    simp only [Set.mem_setOf_eq] at h₁ h₂
    have hi : i₁ = i₂ :=
      decompQuot_eq_of_scalar_fiber b hb_pos hb c hc i₁ i₂ j₁
        (h₁.trans h₂.symm)
    subst hi; rfl
  have h_pos : 0 < HeckeRing.m' (GL_pair 2) D_b D_c D_bc := by
    have h_mem := mem_mulSupport_right_scalar b hb_pos hb c hc hbc
    have h_ne := HeckeRing.m'_pos_of_mem_mulSupport (GL_pair 2) D_b D_c D_bc h_mem
    have : (0 : ℤ) ≤ HeckeRing.m' (GL_pair 2) D_b D_c D_bc := by
      simp only [HeckeRing.m']; exact Nat.cast_nonneg _
    omega
  omega

private lemma m'_right_scalar_eq_zero (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c) (hbc : DivChain 2 (diagMul 2 b (fun _ => c)))
    (A : T' (GL_pair 2)) (hA : A ≠ T_diag 2 (diagMul 2 b (fun _ => c))
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
    T_elem 2 (diagMul 2 b (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc))
      (DivChain_mul 2 b (fun _ => c) hb (divChain_const 2 c)) := by
  set D_b := T_diag 2 b hb_pos hb
  set D_c := T_diag 2 (fun _ => c) (fun _ => hc) (divChain_const 2 c)
  set D_bc := T_diag 2 (diagMul 2 b (fun _ => c)) (diagMul_pos 2 b _ hb_pos (fun _ => hc))
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
  · norm_num [Finsupp.single_apply, h1]
    exact m'_right_scalar_eq_zero b hb_pos hb c hc
      (DivChain_mul 2 b (fun _ => c) hb (divChain_const 2 c)) A h1

/-- T(p,p) commutes with every T_elem. -/
lemma T_pp_comm_T_elem (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i) (ha : DivChain 2 a) :
    T_pp p hp * T_elem 2 a ha_pos ha = T_elem 2 a ha_pos ha * T_pp p hp := by
  unfold T_pp
  rw [T_diag_scalar_mul 2 p hp.pos a ha_pos ha,
      T_elem_mul_scalar a ha_pos ha p hp.pos]
  exact (T_elem_congr_diag 2 (diagMul_scalar_comm a p)
    (diagMul_pos 2 a _ ha_pos (fun _ => hp.pos))
    (diagMul_pos 2 _ a (fun _ => hp.pos) ha_pos)
    (DivChain_mul 2 a _ ha (divChain_const 2 p))
    (DivChain_mul 2 _ _ (divChain_const 2 p) ha)).symm

/-- Powers of T(p,p): `T(p,p)^i = T(p^i, p^i)`. -/
lemma T_pp_pow (i : ℕ) :
    T_pp p hp ^ i =
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
    rw [pow_succ', ih, T_pp]
    rw [T_diag_scalar_mul 2 p hp.pos (fun _ => p ^ i) (fun _ => pow_pos hp.pos i)
      (divChain_const 2 _)]
    exact T_elem_congr_diag 2
      (funext fun _ => by simp [diagMul, pow_succ, mul_comm])
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
    simp only [T_ad']
    rw [dif_neg (by
      intro ⟨_, _, hdvd⟩
      exact absurd (Nat.le_of_dvd (pow_pos hp.pos _) hdvd)
        (not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt (by omega))))])).symm

end Structural

end HeckeRing.GL2
