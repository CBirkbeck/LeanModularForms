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
  if _ : 0 < a ∧ 0 < d ∧ a ∣ d then T_elem ![a, d] else 0

/-- Unfold `T_ad` to `T_elem` when all positivity and divisibility conditions hold. -/
lemma T_ad_of_pos (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (h : a ∣ d) :
    T_ad a d = T_elem ![a, d] :=
  dif_pos ⟨ha, hd, h⟩

/-- `T_ad a d` is zero when the positivity or divisibility conditions fail. -/
lemma T_ad_eq_zero {a d : ℕ} (h : ¬(0 < a ∧ 0 < d ∧ a ∣ d)) : T_ad a d = 0 :=
  dif_neg h

/-- `T(p,p)`: the scalar double coset for prime `p`, equal to `T_ad p p`. -/
noncomputable def T_pp (p : ℕ) : HeckeAlgebra 2 := T_ad p p

/-- For `p` prime, `T(p,p)` equals the scalar diagonal element `T_elem(p,p)`. -/
lemma T_pp_of_pos (p : ℕ) (hp : p.Prime) : T_pp p = T_elem (fun _ : Fin 2 => p) := by
  simp only [T_pp, T_ad_of_pos p p hp.pos hp.pos (dvd_refl _)]
  exact T_elem_congr_diag 2 (funext fun i => by fin_cases i <;> rfl)

/-- `T(p,p)` is definitionally equal to `T_ad p p`. -/
lemma T_pp_eq_T_ad (p : ℕ) : T_pp p = T_ad p p := rfl

/-- The all-ones diagonal element is the identity in the Hecke algebra. -/
lemma T_elem_ones_eq : T_elem (fun _ : Fin 2 => 1) = 1 := by
  show T_single (GL_pair 2) ℤ (T_diag (fun _ : Fin 2 => 1)) 1 = 1
  rw [T_diag_ones]; exact (one_def (GL_pair 2) (Z := ℤ)).symm

/-- T(1,1) is the identity element. -/
@[simp] lemma T_ad_one_one : T_ad 1 1 = 1 := by
  rw [T_ad_of_pos 1 1 Nat.one_pos Nat.one_pos (dvd_refl _)]
  exact (T_elem_congr_diag 2
    (funext fun i => by fin_cases i <;> rfl)).trans T_elem_ones_eq

/-- `T(m) = Σ_{a | m} T(a, m/a)`. -/
noncomputable def T_sum (m : ℕ+) : HeckeAlgebra 2 :=
  ∑ a ∈ (m : ℕ).divisors, T_ad a ((m : ℕ) / a)

section Structural

variable (p : ℕ) (hp : p.Prime)

private lemma doubleCoset_eq_of_mem' (g δ : GL (Fin 2) ℚ)
    (h : g ∈ DoubleCoset.doubleCoset δ (SLnZ_subgroup 2) (SLnZ_subgroup 2)) :
    DoubleCoset.doubleCoset g (SLnZ_subgroup 2) (SLnZ_subgroup 2) =
      DoubleCoset.doubleCoset δ (SLnZ_subgroup 2) (SLnZ_subgroup 2) := by
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := DoubleCoset.mem_doubleCoset.mp h
  rw [heq]
  exact (doubleCoset_mul_right_eq_self (GL_pair 2) ⟨h₂, hh₂⟩ (h₁ * δ)).trans
    (doset_mul_left_eq_self (GL_pair 2) ⟨h₁, hh₁⟩ δ)

/-- For p prime, T(p) = T_ad(1,p). -/
lemma T_sum_prime : T_sum ⟨p, hp.pos⟩ = T_ad 1 p := by
  show ∑ a ∈ p.divisors, T_ad a (p / a) = _
  rw [hp.sum_divisors, Nat.div_self hp.pos, Nat.div_one]
  have h1 : T_ad p 1 = 0 := T_ad_eq_zero (by
    push_neg; exact fun _ _ hdvd => hp.one_lt.not_ge (Nat.le_of_dvd Nat.one_pos hdvd))
  rw [h1, zero_add]

private lemma diagMul_scalar_comm (b : Fin 2 → ℕ) (c : ℕ) :
    b * (fun _ => c) = (fun _ => c) * b :=
  funext fun _ => Nat.mul_comm _ _

private lemma scalar_product_mem_doubleCoset
    (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (_hb : DivChain 2 b) (c : ℕ) (hc : 0 < c)
    (x1 db x2 dc : GL (Fin 2) ℚ)
    (h₁b : GL (Fin 2) ℚ) (hh₁b : h₁b ∈ (GL_pair 2).H)
    (h₂b : GL (Fin 2) ℚ) (hh₂b : h₂b ∈ (GL_pair 2).H)
    (h₁c : GL (Fin 2) ℚ) (hh₁c : h₁c ∈ (GL_pair 2).H)
    (h₂c : GL (Fin 2) ℚ) (hh₂c : h₂c ∈ (GL_pair 2).H)
    (hx1 : x1 ∈ (GL_pair 2).H) (hx2 : x2 ∈ (GL_pair 2).H)
    (hδb_eq : db = h₁b * diagMat 2 b * h₂b)
    (hδc_eq : dc = h₁c * diagMat 2 (fun _ => c) * h₂c) :
    x1 * db * (x2 * dc) ∈ DoubleCoset.doubleCoset
      (diagMat 2 (b * (fun _ => c)) : GL (Fin 2) ℚ) (GL_pair 2).H (GL_pair 2).H := by
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨x1 * h₁b, (GL_pair 2).H.mul_mem hx1 hh₁b,
          h₂b * x2 * h₁c * h₂c,
          (GL_pair 2).H.mul_mem ((GL_pair 2).H.mul_mem
            ((GL_pair 2).H.mul_mem hh₂b hx2) hh₁c) hh₂c, ?_⟩
  rw [hδb_eq, hδc_eq]
  have h_comm := diagMat_scalar_comm 2 c hc (h₂b * x2 * h₁c)
  calc x1 * (h₁b * diagMat 2 b * h₂b) *
      (x2 * (h₁c * diagMat 2 (fun _ => c) * h₂c))
      = x1 * h₁b * (diagMat 2 b * (h₂b * x2 * h₁c)) *
        (diagMat 2 (fun _ => c) * h₂c) := by group
    _ = x1 * h₁b * (diagMat 2 b *
          (diagMat 2 (fun _ => c) * (h₂b * x2 * h₁c))) * h₂c := by
        have : (h₂b * x2 * h₁c) * diagMat 2 (fun _ => c) =
            diagMat 2 (fun _ => c) * (h₂b * x2 * h₁c) := h_comm.symm
        calc x1 * h₁b * (diagMat 2 b * (h₂b * x2 * h₁c)) *
            (diagMat 2 (fun _ => c) * h₂c)
            = x1 * h₁b * (diagMat 2 b *
                ((h₂b * x2 * h₁c) * diagMat 2 (fun _ => c))) * h₂c := by group
          _ = x1 * h₁b * (diagMat 2 b *
                (diagMat 2 (fun _ => c) * (h₂b * x2 * h₁c))) * h₂c := by rw [this]
    _ = x1 * h₁b * (diagMat 2 (b * (fun _ => c)) *
          (h₂b * x2 * h₁c)) * h₂c := by
        rw [show diagMat 2 b * (diagMat 2 (fun _ => c) * (h₂b * x2 * h₁c)) =
            (diagMat 2 b * diagMat 2 (fun _ => c)) * (h₂b * x2 * h₁c) from by group,
          diagMat_mul 2 b (fun _ => c) hb_pos (fun _ => hc)]
    _ = x1 * h₁b * diagMat 2 (b * (fun _ => c)) *
        (h₂b * x2 * h₁c * h₂c) := by group

private lemma mulMap_right_scalar_eq (b : Fin 2 → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb : DivChain 2 b)
    (c : ℕ) (hc : 0 < c) (_hbc : DivChain 2 (b * (fun _ => c)))
    (p : decompQuot (GL_pair 2) (HeckeCoset.rep (T_diag b)) ×
         decompQuot (GL_pair 2) (HeckeCoset.rep (T_diag (fun _ : Fin 2 => c)))) :
    mulMap (GL_pair 2) (HeckeCoset.rep (T_diag b))
      (HeckeCoset.rep (T_diag (fun _ : Fin 2 => c))) p =
      T_diag (b * (fun _ => c)) := by
  sorry

private lemma scalar_coset_rep_normalizes (c : ℕ) (hc : 0 < c) :
    let D_c := T_diag (fun _ : Fin 2 => c)
    let H' := (GL_pair 2).H
    let δ_c := (HeckeCoset.rep D_c : GL (Fin 2) ℚ)
    ({δ_c} : Set (GL (Fin 2) ℚ)) * (H' : Set (GL (Fin 2) ℚ)) =
    (H' : Set (GL (Fin 2) ℚ)) * {δ_c} := by
  sorry

private lemma mem_mulSupport_right_scalar (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c) (hbc : DivChain 2 (b * (fun _ => c))) :
    let D_b := T_diag b
    let D_c := T_diag (fun _ : Fin 2 => c)
    let D_bc := T_diag (b * (fun _ => c))
    D_bc ∈ HeckeRing.mulSupport (GL_pair 2)
      (HeckeCoset.rep D_b) (HeckeCoset.rep D_c) := by
  sorry

private lemma heckeMultiplicity_right_scalar_eq_one (b : Fin 2 → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb : DivChain 2 b)
    (c : ℕ) (hc : 0 < c) (hbc : DivChain 2 (b * (fun _ => c)))
    (D_b : HeckeCoset (GL_pair 2)) (hDb : D_b = T_diag b)
    (D_c : HeckeCoset (GL_pair 2)) (hDc : D_c = T_diag (fun _ : Fin 2 => c))
    (D_bc : HeckeCoset (GL_pair 2)) (hDbc : D_bc = T_diag (b * (fun _ => c))) :
    HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep D_b)
      (HeckeCoset.rep D_c) (HeckeCoset.rep D_bc) = 1 := by
  sorry

private lemma heckeMultiplicity_right_scalar_eq_zero (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c) (hbc : DivChain 2 (b * (fun _ => c)))
    (A : HeckeCoset (GL_pair 2)) (hA : A ≠ T_diag (b * (fun _ : Fin 2 => c))) :
    HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep (T_diag b))
      (HeckeCoset.rep (T_diag (fun _ : Fin 2 => c))) (HeckeCoset.rep A) = 0 := by
  sorry

/-- Multiplication by a scalar diagonal element: `T_elem(b) * T_elem(c,c) = T_elem(b * c)`. -/
theorem T_elem_mul_scalar (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c) :
    T_elem b * T_elem (fun _ : Fin 2 => c) = T_elem (b * (fun _ => c)) := by
  sorry

/-- `T(p,p)` commutes with every diagonal element `T_elem(a)` for `p` prime. -/
lemma T_pp_comm_T_elem (p : ℕ) (hp : p.Prime) (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i)
    (ha : DivChain 2 a) : T_pp p * T_elem a = T_elem a * T_pp p := by
  rw [T_pp_of_pos p hp, T_diag_scalar_mul 2 p hp.pos a ha_pos ha,
    T_elem_mul_scalar a ha_pos ha p hp.pos]
  exact (T_elem_congr_diag 2 (diagMul_scalar_comm a p)).symm

include hp in
/-- `T(p,p)^i = T_elem(p^i, p^i)`: the `i`-th power of the scalar double coset. -/
lemma T_pp_pow (i : ℕ) : T_pp p ^ i = T_elem (fun _ : Fin 2 => p ^ i) := by
  induction i with
  | zero =>
    simp only [pow_zero]; symm
    exact (T_elem_congr_diag 2 (funext fun _ => by simp)).trans T_elem_ones_eq
  | succ i ih =>
    rw [pow_succ', ih, T_pp_of_pos p hp, T_diag_scalar_mul 2 p hp.pos (fun _ => p ^ i)
      (fun _ => pow_pos hp.pos i) (divChain_const 2 _)]
    exact T_elem_congr_diag 2 (funext fun _ => by simp [Pi.mul_apply, pow_succ, mul_comm])

/-- Expand `T(p^k)` as a sum over divisor pairs with non-zero `T_ad` terms. -/
lemma T_sum_ppow_expansion (k : ℕ) :
    T_sum ⟨p ^ k, pow_pos hp.pos k⟩ =
    ∑ i ∈ Finset.range (k / 2 + 1), T_ad (p ^ i) (p ^ (k - i)) := by
  show ∑ a ∈ (p ^ k).divisors, T_ad a (p ^ k / a) = _
  rw [Nat.sum_divisors_prime_pow hp]
  have h_div : ∀ j ∈ Finset.range (k + 1),
      T_ad (p ^ j) (p ^ k / p ^ j) = T_ad (p ^ j) (p ^ (k - j)) :=
    fun j hj => by rw [Finset.mem_range] at hj; congr 1; exact Nat.pow_div (by omega) hp.pos
  rw [Finset.sum_congr rfl h_div]
  exact (Finset.sum_subset (Finset.range_mono (by omega)) (fun j hj hnj => by
    simp only [Finset.mem_range] at hj hnj; apply T_ad_eq_zero; push_neg; intro _ _
    exact fun hdvd => absurd (Nat.le_of_dvd (pow_pos hp.pos _) hdvd)
      (not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt (by omega))))).symm

end Structural

end HeckeRing.GL2
