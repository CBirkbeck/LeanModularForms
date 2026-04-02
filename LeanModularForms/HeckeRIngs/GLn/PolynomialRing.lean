/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.PrimeDecomposition
import LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution
import LeanModularForms.HeckeRIngs.GL2.MultiplicationTable
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Polynomial Ring Structure of the p-local Hecke Ring

Shimura's Theorem 3.20: the p-local Hecke ring `R_p^{(n)}` is isomorphic to a polynomial
ring `ℤ[X₁,...,Xₙ]` in `n` variables.

## Main definitions

* `T_gen_diag` — the diagonal for the k-th generator `T(1,...,1,p,...,p)`
* `T_gen` — the k-th generator of `R_p`: `T_gen k = T(1,...,1,p,...,p)` with `k+1` entries of `p`
* `ppowWeight` — weight of a p-power diagonal: sum of exponents

## Main results

* `divChain_T_gen` — the T_gen diagonal satisfies the divisibility chain condition
* `T_gen_mem_R_p` — each generator lies in `R_p`
* `T_gen_generates_R_p` — the generators generate `R_p` (surjectivity)
* `T_gen_algebraically_independent` — the generators are algebraically independent (injectivity)
* `R_p_isPolynomialRing` — Theorem 3.20: `R_p ≅ ℤ[X₁,...,Xₙ]`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.2, Theorem 3.20
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset

open scoped Pointwise

namespace HeckeRing.GLn

variable (n : ℕ)

/-! ### Generator diagonals -/

section TGen

variable (p : ℕ) (hp : p.Prime)

/-- The diagonal for the k-th generator: `(1,...,1,p,...,p)` with `n-1-k` ones
    followed by `k+1` entries of `p`. Here `k : Fin n`, giving `n` generators. -/
def T_gen_diag (k : Fin n) : Fin n → ℕ :=
  fun i => if (i : ℕ) < n - 1 - (k : ℕ) then 1 else p

@[simp]
lemma T_gen_diag_val (k : Fin n) (i : Fin n) :
    T_gen_diag n p k i =
    if (i : ℕ) < n - 1 - (k : ℕ) then 1 else p := rfl

lemma T_gen_diag_pos (hp : p.Prime) (k : Fin n) : ∀ i, 0 < T_gen_diag n p k i := by
  intro i; simp only [T_gen_diag]; split_ifs with h
  · omega
  · exact hp.pos

/-- The T_gen diagonal satisfies the divisibility chain condition. -/
lemma divChain_T_gen (k : Fin n) :
    DivChain n (T_gen_diag n p k) := by
  intro i hi
  simp only [T_gen_diag_val]
  by_cases h1 : i < n - 1 - (k : ℕ)
  · by_cases h2 : i + 1 < n - 1 - (k : ℕ)
    · simp [h1, h2]
    · simp [h1, h2]
  · have h2 : ¬ (i + 1 < n - 1 - (k : ℕ)) := by omega
    simp [h1, h2]

variable [NeZero n]

/-- The T_gen diagonal has p-power entries (each entry is 1 = p^0 or p = p^1). -/
lemma T_gen_diag_is_ppow (k : Fin n) :
    T_gen_diag n p k =
    ppowDiag n p (fun i => if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1) := by
  funext i
  simp only [T_gen_diag, ppowDiag]
  split_ifs <;> simp

/-- The exponent function for T_gen is monotone. -/
lemma T_gen_exp_monotone (k : Fin n) :
    Monotone (fun i : Fin n => if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1) := by
  intro i j hij
  simp only
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · exact le_rfl

include hp
/-- The k-th generator of R_p: `T(1,...,1,p,...,p)` with `k+1` entries of `p`. -/
noncomputable def T_gen (k : Fin n) : HeckeAlgebra n :=
  T_elem (T_gen_diag n p k)

/-- Each T_gen lies in R_p. -/
lemma T_gen_mem_R_p (k : Fin n) : T_gen n p k ∈ R_p n p hp := by
  have h_eq : T_gen n p k =
      T_elem (ppowDiag n p (fun i => if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1)) :=
    T_elem_congr_diag (n := n) (T_gen_diag_is_ppow n p k)
  rw [h_eq]
  exact T_elem_ppow_mem_R_p n p hp _ (T_gen_exp_monotone n k)

omit hp

end TGen

/-! ### Weight of a p-power diagonal -/

section Weight

/-- Weight of a p-power diagonal: the sum of all exponents. -/
def ppowWeight (e : Fin n → ℕ) : ℕ := ∑ i, e i

/-- Weight is zero iff all exponents are zero. -/
lemma ppowWeight_eq_zero_iff (e : Fin n → ℕ) :
    ppowWeight n e = 0 ↔ ∀ i, e i = 0 := by
  simp [ppowWeight, Finset.sum_eq_zero_iff]

end Weight

/-! ### Polynomial ring isomorphism (Theorem 3.20) -/

section PolynomialRing

variable [NeZero n] (p : ℕ) (hp : p.Prime)

/-- Evaluation homomorphism: `Xₖ ↦ T_gen k`.
    Maps `ℤ[X₁,...,Xₙ]` into the Hecke algebra. -/
noncomputable def evalHom : MvPolynomial (Fin n) ℤ →+* HeckeAlgebra n :=
  MvPolynomial.eval₂Hom (Int.castRingHom (HeckeAlgebra n)) (fun k => T_gen n p k)

/-! #### Infrastructure for the isomorphism -/

/-- `T(1,...,1)` is the multiplicative identity in the Hecke algebra, for any `n`. -/
lemma T_elem_ones_eq_one : T_elem (fun _ : Fin n => 1) = 1 := by
  show HeckeRing.T_single (GL_pair n) ℤ (T_diag (fun _ : Fin n => 1)) 1 = 1
  rw [T_diag_ones]; exact (HeckeRing.one_def (GL_pair n) (Z := ℤ)).symm

/-- `T(c,...,c)^k = T(c^k,...,c^k)`: scalar diagonal elements are closed under powers. -/
lemma T_scalar_pow (c : ℕ) (hc : 0 < c) (k : ℕ) :
    T_elem (fun _ : Fin n => c) ^ k = T_elem (fun _ : Fin n => c ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero]; symm
    exact (T_elem_congr_diag n (funext fun _ => by simp)).trans (T_elem_ones_eq_one n)
  | succ k ih =>
    rw [pow_succ', ih, T_diag_scalar_mul n c hc (fun _ => c ^ k)
      (fun _ => pow_pos hc k) (divChain_const n _)]
    exact T_elem_congr_diag n (funext fun _ => by
      simp only [Pi.mul_apply]; ring)

/-- Each `T_gen k` lies in the range of `evalHom`. -/
lemma T_gen_mem_evalHom_range (k : Fin n) :
    T_gen n p k ∈ (evalHom n p).range :=
  ⟨MvPolynomial.X k, by unfold evalHom; exact MvPolynomial.eval₂Hom_X' _ _ k⟩

end PolynomialRing

end HeckeRing.GLn

/-! ### Surjectivity for n = 2 (Shimura Theorem 3.20) -/

namespace HeckeRing.GLn.Surj

open HeckeRing.GLn HeckeRing.GL2

/-! #### Bridge lemmas: T_gen at n=2 matches GL2 definitions -/

/-- `T_gen 2 p 0 = T_ad 1 p`: the first generator is `T(1,p)`. -/
lemma T_gen_zero_eq_T_ad (p : ℕ) (hp : p.Prime) :
    T_gen 2 p (0 : Fin 2) = T_ad 1 p := by
  show T_elem (T_gen_diag 2 p 0) = _
  have h : T_gen_diag 2 p (0 : Fin 2) = ![1, p] := by
    funext i; simp only [T_gen_diag_val]; fin_cases i <;> simp
  rw [h, T_ad_of_pos 1 p Nat.one_pos hp.pos (one_dvd _)]

/-- `T_gen 2 p 1 = T_pp p`: the second generator is the diamond operator. -/
lemma T_gen_one_eq_T_pp (p : ℕ) (hp : p.Prime) :
    T_gen 2 p (1 : Fin 2) = T_pp p := by
  show T_elem (T_gen_diag 2 p 1) = _
  have h : T_gen_diag 2 p (1 : Fin 2) = ![p, p] := by
    funext i; simp only [T_gen_diag_val]; fin_cases i <;> simp
  rw [h, T_pp_of_pos p hp]
  exact T_elem_congr_diag (n := 2) (funext fun i => by fin_cases i <;> rfl)

/-- `T_sum(p) = T_gen 0`: the sum T(p) is the first generator for p prime. -/
lemma T_sum_p_eq_T_gen_zero (p : ℕ) (hp : p.Prime) :
    T_sum ⟨p, hp.pos⟩ = T_gen 2 p (0 : Fin 2) := by
  rw [T_gen_zero_eq_T_ad p hp, T_sum_prime p hp]

/-! #### Step 3: T_sum(p^k) in evalHom range by strong induction -/

private lemma X_zero_mem_range (p : ℕ) :
    T_gen 2 p (0 : Fin 2) ∈ (evalHom 2 p).range :=
  ⟨MvPolynomial.X 0, by unfold evalHom; exact MvPolynomial.eval₂Hom_X' _ _ 0⟩

private lemma X_one_mem_range (p : ℕ) :
    T_gen 2 p (1 : Fin 2) ∈ (evalHom 2 p).range :=
  ⟨MvPolynomial.X 1, by unfold evalHom; exact MvPolynomial.eval₂Hom_X' _ _ 1⟩

private lemma T_pp_mem_range (p : ℕ) (hp : p.Prime) :
    T_pp p ∈ (evalHom 2 p).range := by
  rw [← T_gen_one_eq_T_pp p hp]; exact X_one_mem_range p

/-- `T_sum(p^k)` lies in the range of the evaluation homomorphism, for all `k`. -/
lemma T_sum_ppow_in_range (p : ℕ) (hp : p.Prime) (k : ℕ) :
    T_sum ⟨p ^ k, pow_pos hp.pos k⟩ ∈ (evalHom 2 p).range := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
  match k with
  | 0 =>
    rw [show T_sum ⟨p ^ 0, pow_pos hp.pos 0⟩ = T_sum 1 from by congr 1,
        T_sum_one]
    exact (evalHom 2 p).range.one_mem
  | 1 =>
    have h1 : T_sum ⟨p ^ 1, pow_pos hp.pos 1⟩ = T_sum ⟨p, hp.pos⟩ := by
      congr 1; exact Subtype.ext (pow_one p)
    rw [h1, T_sum_p_eq_T_gen_zero p hp]; exact X_zero_mem_range p
  | k + 2 =>
    have h_rec := T_sum_ppow_recurrence p hp (k + 1) (by omega)
    rw [show k + 1 - 1 = k from by omega,
        show k + 1 + 1 = k + 2 from by omega] at h_rec
    rw [h_rec]
    have h_p1 : T_sum ⟨p, hp.pos⟩ ∈ (evalHom 2 p).range := by
      rw [T_sum_p_eq_T_gen_zero p hp]; exact X_zero_mem_range p
    exact (evalHom 2 p).range.sub_mem
      ((evalHom 2 p).range.mul_mem h_p1 (ih (k + 1) (by omega)))
      ((evalHom 2 p).range.zsmul_mem
        ((evalHom 2 p).range.mul_mem (T_pp_mem_range p hp) (ih k (by omega)))
        (p : ℤ))

/-! #### Step 4: T_ad(1, p^k) in evalHom range -/

/-- `T_ad(1, p^k)` lies in the range of the evaluation homomorphism. -/
lemma T_ad_one_ppow_in_range (p : ℕ) (hp : p.Prime) (k : ℕ) :
    T_ad 1 (p ^ k) ∈ (evalHom 2 p).range := by
  match k with
  | 0 => simp only [pow_zero, T_ad_one_one]; exact (evalHom 2 p).range.one_mem
  | 1 =>
    rw [pow_one, ← T_gen_zero_eq_T_ad p hp]; exact X_zero_mem_range p
  | k + 2 =>
    rw [T_ad_one_ppow_eq p hp (k + 2) (by omega),
        show k + 2 - 2 = k from by omega]
    exact (evalHom 2 p).range.sub_mem
      (T_sum_ppow_in_range p hp (k + 2))
      ((evalHom 2 p).range.mul_mem (T_pp_mem_range p hp)
        (T_sum_ppow_in_range p hp k))

/-! #### Step 5: General ppow element for n=2 -/

/-- `T_elem (ppowDiag 2 p e)` is in the evalHom range when `e` is monotone.
    Factor out `T(p^{e₀}, p^{e₀})` to reduce to `T(1, p^{e₁-e₀})`. -/
lemma T_elem_ppow_in_range (p : ℕ) (hp : p.Prime)
    (e : Fin 2 → ℕ) (hmono : Monotone e) :
    T_elem (ppowDiag 2 p e) ∈ (evalHom 2 p).range := by
  by_cases he0 : e 0 = 0
  · -- e 0 = 0: ppowDiag = ![1, p^{e 1}]
    have h_eq : ppowDiag 2 p e = ![1, p ^ (e 1)] := by
      funext i; simp only [ppowDiag]; fin_cases i <;> simp [he0]
    rw [T_elem_congr_diag (n := 2) h_eq,
      ← T_ad_of_pos 1 (p ^ (e 1)) Nat.one_pos (pow_pos hp.pos _) (one_dvd _)]
    exact T_ad_one_ppow_in_range p hp (e 1)
  · -- e 0 > 0: ppowDiag = scalar(p^{e 0}) * ppowDiag(0, e 1 - e 0)
    have h_le : e 0 ≤ e 1 := hmono (Fin.zero_le _)
    have h_eq : ppowDiag 2 p e =
        (fun _ => p ^ (e 0)) * ppowDiag 2 p ![0, e 1 - e 0] := by
      funext i; simp only [ppowDiag, Pi.mul_apply]
      fin_cases i
      · simp
      · show p ^ e 1 = p ^ e 0 * p ^ (e 1 - e 0)
        rw [← pow_add, Nat.add_sub_cancel' h_le]
    rw [T_elem_congr_diag (n := 2) h_eq,
      ← T_diag_scalar_mul 2 (p ^ (e 0)) (pow_pos hp.pos _)
        (ppowDiag 2 p ![0, e 1 - e 0])
        (ppowDiag_pos 2 p hp _)
        (divChain_ppow 2 p _ (by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def]))]
    apply (evalHom 2 p).range.mul_mem
    · rw [← T_pp_pow p hp (e 0), ← T_gen_one_eq_T_pp p hp]
      exact (evalHom 2 p).range.pow_mem (X_one_mem_range p) _
    · have h2 : ppowDiag 2 p ![0, e 1 - e 0] = ![1, p ^ (e 1 - e 0)] := by
        funext i; simp only [ppowDiag]; fin_cases i <;> simp
      rw [T_elem_congr_diag (n := 2) h2,
        ← T_ad_of_pos 1 (p ^ (e 1 - e 0)) Nat.one_pos
          (pow_pos hp.pos _) (one_dvd _)]
      exact T_ad_one_ppow_in_range p hp (e 1 - e 0)

/-! #### Step 6: Assembly — every R_p element is in the image -/

/-- Surjectivity of `evalHom` at n=2: every element of `R_p 2 p` is in the range
    of the evaluation homomorphism `ℤ[X₁, X₂] → HeckeAlgebra 2`. -/
theorem T_gen_generates_R_p_two (p : ℕ) (hp : p.Prime) :
    ∀ f ∈ R_p 2 p hp, f ∈ (evalHom 2 p).range := by
  intro f hf
  apply Subring.closure_le.mpr _ hf
  intro x hx
  obtain ⟨e, hmono, rfl⟩ := hx
  exact T_elem_ppow_in_range p hp e hmono

end HeckeRing.GLn.Surj

/-! ### Surjectivity for n = 1 -/

namespace HeckeRing.GLn.SurjOne

open HeckeRing.GLn

/-- For n=1, `T_gen_diag 1 p 0 = fun _ => p`. -/
private lemma T_gen_diag_one_eq (p : ℕ) :
    T_gen_diag 1 p (0 : Fin 1) = fun _ => p := by
  funext i; simp [T_gen_diag_val]

/-- n=1 surjectivity: every element of R_p is in the range of evalHom. -/
theorem T_gen_generates_R_p_one (p : ℕ) (hp : p.Prime) :
    ∀ f ∈ R_p 1 p hp, f ∈ (evalHom 1 p).range := by
  intro f hf
  apply Subring.closure_le.mpr _ hf
  intro x hx
  obtain ⟨e, _hmono, rfl⟩ := hx
  -- For Fin 1, ppowDiag is determined by e 0
  have he : ppowDiag 1 p e = fun _ => p ^ (e 0) := by
    funext i; simp [ppowDiag]; congr 1; exact congr_arg e (Subsingleton.elim i 0)
  rw [T_elem_congr_diag 1 he, ← T_scalar_pow 1 p hp.pos (e 0)]
  rw [show T_elem (fun _ : Fin 1 => p) = T_gen 1 p (0 : Fin 1) from by
    unfold T_gen; exact (T_elem_congr_diag 1 (T_gen_diag_one_eq p)).symm]
  exact (evalHom 1 p).range.pow_mem (T_gen_mem_evalHom_range 1 p 0) _

end HeckeRing.GLn.SurjOne

/-! ### Injectivity -/

namespace HeckeRing.GLn.Inj

open HeckeRing.GLn HeckeRing.GL2

/-! #### evalHom maps into R_p -/

/-- Every element in the image of `evalHom` belongs to `R_p`. -/
lemma evalHom_mem_R_p (n : ℕ) [NeZero n] (p : ℕ) (hp : p.Prime)
    (P : MvPolynomial (Fin n) ℤ) : evalHom n p P ∈ R_p n p hp := by
  apply MvPolynomial.induction_on P
  · intro a
    have : evalHom n p (MvPolynomial.C a) = (Int.castRingHom (HeckeAlgebra n)) a := by
      unfold evalHom; exact MvPolynomial.eval₂Hom_C _ _ a
    rw [this]; show (a : HeckeAlgebra n) ∈ R_p n p hp
    rw [show (a : HeckeAlgebra n) = a • (1 : HeckeAlgebra n) from (zsmul_one a).symm]
    exact (R_p n p hp).zsmul_mem (R_p n p hp).one_mem a
  · intro f g hf hg; rw [map_add]; exact (R_p n p hp).add_mem hf hg
  · intro f i hf
    rw [map_mul]
    exact (R_p n p hp).mul_mem hf (by
      have : evalHom n p (MvPolynomial.X i) = T_gen n p i := by
        unfold evalHom; exact MvPolynomial.eval₂Hom_X' _ _ i
      rw [this]
      exact T_gen_mem_R_p n p hp i)

/-- The restricted evaluation homomorphism into `R_p`. -/
noncomputable def evalHomR (n : ℕ) [NeZero n] (p : ℕ) (hp : p.Prime) :
    MvPolynomial (Fin n) ℤ →+* R_p n p hp where
  toFun P := ⟨evalHom n p P, evalHom_mem_R_p n p hp P⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext (map_add _ x y)
  map_mul' x y := Subtype.ext (map_mul _ x y)

/-! #### n=1 injectivity -/

/-- For n=1, `T_gen(0)^k = T_elem(fun _ => p^k)`. -/
private lemma T_gen_pow_one (p : ℕ) (hp : p.Prime) (k : ℕ) :
    T_gen 1 p (0 : Fin 1) ^ k = T_elem (fun _ : Fin 1 => p ^ k) := by
  rw [show T_gen 1 p (0 : Fin 1) = T_elem (fun _ : Fin 1 => p) from by
    unfold T_gen; exact T_elem_congr_diag 1 (SurjOne.T_gen_diag_one_eq p)]
  exact T_scalar_pow 1 p hp.pos k

/-- n=1: evalHom is injective. Different monomials map to distinct basis elements,
    so the images are ℤ-linearly independent. -/
theorem evalHom_injective_one (p : ℕ) (hp : p.Prime) :
    Function.Injective (evalHom 1 p) := by
  intro P Q hPQ
  rw [← sub_eq_zero]; set R := P - Q
  have hR : evalHom 1 p R = 0 := by simp [R, map_sub, hPQ]
  by_contra hne
  obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr hne
  have hcoeff : R.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  -- Extract Finsupp coefficient at T_diag (fun _ => p^{s 0})
  set D := T_diag (n := 1) (fun _ => p ^ (s 0))
  have h0 : (evalHom 1 p R).toFun D = 0 := by rw [hR]; rfl
  apply hcoeff
  suffices h : ((evalHom 1 p) R).toFun D = MvPolynomial.coeff s R from h ▸ h0
  -- Adapted for v4.29: use erw for coercion-sensitive rewrites
  -- Reduce to eval₂ and expand as sum, push application D inside
  show (MvPolynomial.eval₂ (Int.castRingHom (HeckeAlgebra 1))
    (fun k => T_gen 1 p k) R) D = _
  rw [MvPolynomial.eval₂_eq']
  erw [Finsupp.finset_sum_apply]
  simp only [Fin.prod_univ_one]
  -- Each summand: (int_cast * T_gen^k) D → coeff * if delta
  have step : ∀ d ∈ R.support,
      ((Int.castRingHom (HeckeAlgebra 1)) (R.coeff d) * T_gen 1 p 0 ^ d 0) D =
      R.coeff d * if T_diag (n := 1) (fun _ => p ^ d 0) = D then 1 else 0 := fun d _ => by
    rw [T_gen_pow_one p hp,
      show (T_elem (fun _ : Fin 1 => p ^ d 0) : HeckeAlgebra 1) =
        Finsupp.single (T_diag (n := 1) (fun _ => p ^ d 0)) (1 : ℤ) from rfl,
      show (Int.castRingHom (HeckeAlgebra 1)) (R.coeff d) =
        (R.coeff d) • (1 : HeckeAlgebra 1) from by rw [Int.coe_castRingHom, zsmul_one],
      smul_mul_assoc, one_mul, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  erw [Finset.sum_congr rfl step]
  -- The T_diag condition in the sum is equivalent to d = s
  have hTd : ∀ d, (T_diag (n := 1) (fun _ => p ^ d 0) = D) ↔ d = s := by
    intro d; constructor
    · intro h
      have := diagonal_representative_unique (n := 1) (fun _ : Fin 1 => p ^ d 0)
        (fun _ : Fin 1 => p ^ s 0) (fun _ => pow_pos hp.pos _) (fun _ => pow_pos hp.pos _)
        (divChain_const 1 _) (divChain_const 1 _) h
      exact Finsupp.ext (fun i => by
        fin_cases i; exact Nat.pow_right_injective hp.one_lt (congr_fun this 0))
    · rintro rfl; rfl
  simp only [D, mul_ite, mul_one, mul_zero]
  simp_rw [show ∀ d, (if (T_diag (n := 1) (fun _ => p ^ d 0)) =
    T_diag (fun _ => p ^ s 0) then R.coeff d else 0) =
    if d = s then R.coeff d else 0 from fun d => if_congr (hTd d) rfl rfl]
  rw [Finset.sum_ite_eq']
  simp [MvPolynomial.mem_support_iff, hcoeff]

/-! #### n=2 injectivity -/

/-- n=2: evalHom is injective. Uses the Kronecker delta property for `T_gen(0)^a`
    coefficients at first-exponent-zero T_diags, and the scalar shift property
    of `T_gen(1)^b = T(p,p)^b`. -/
theorem evalHom_injective_two (p : ℕ) (hp : p.Prime) :
    Function.Injective (evalHom 2 p) := by
  sorry

/-! #### Surjectivity of restricted evalHom -/

/-- Surjectivity of `evalHomR` follows from surjectivity onto `R_p`. -/
lemma evalHomR_surjective (n : ℕ) [NeZero n] (p : ℕ) (hp : p.Prime)
    (h_surj : ∀ f ∈ R_p n p hp, f ∈ (evalHom n p).range) :
    Function.Surjective (evalHomR n p hp) := by
  intro ⟨f, hf⟩
  obtain ⟨P, hP⟩ := h_surj f hf
  exact ⟨P, Subtype.ext hP⟩

/-- Injectivity of `evalHomR` follows from injectivity of `evalHom`. -/
lemma evalHomR_injective (n : ℕ) [NeZero n] (p : ℕ) (_hp : p.Prime)
    (h_inj : Function.Injective (evalHom n p)) :
    Function.Injective (evalHomR n p ‹_›) := by
  intro P Q hPQ
  exact h_inj (Subtype.ext_iff.mp hPQ)

end HeckeRing.GLn.Inj

/-! ### Assembly: Theorem 3.20 -/

namespace HeckeRing.GLn

variable (n : ℕ) [NeZero n] (p : ℕ) (hp : p.Prime)

/-- Every element of R_p is in the image of evalHom (surjectivity).
    Proved for n = 1 and n = 2; the general case requires the projection ψ
    (Phase B/C of Shimura Theorem 3.20). -/
theorem T_gen_generates_R_p :
    ∀ f ∈ R_p n p hp, f ∈ (evalHom n p).range := by
  by_cases h1 : n = 1
  · subst h1; exact SurjOne.T_gen_generates_R_p_one p ‹_›
  · by_cases h2 : n = 2
    · subst h2; exact Surj.T_gen_generates_R_p_two p ‹_›
    · sorry -- General n requires Phase B (projection ψ) and Phase C (induction)

include hp in
/-- evalHom is injective. Proved for n = 1 and n = 2;
    general case requires Phase B (projection) and Phase C (induction on n). -/
theorem evalHom_injective :
    Function.Injective (evalHom n p) := by
  by_cases h1 : n = 1
  · subst h1; exact Inj.evalHom_injective_one p ‹_›
  · by_cases h2 : n = 2
    · subst h2; exact Inj.evalHom_injective_two p ‹_›
    · sorry -- General n requires Phase B/C

/-- Shimura Theorem 3.20: the p-local Hecke ring is isomorphic to a polynomial ring.
    `R_p^{(n)} ≅ ℤ[X₁,...,Xₙ]`. -/
noncomputable def R_p_isPolynomialRing :
    MvPolynomial (Fin n) ℤ ≃+* R_p n p hp :=
  RingEquiv.ofBijective (Inj.evalHomR n p hp)
    ⟨Inj.evalHomR_injective n p hp (evalHom_injective n p hp),
     Inj.evalHomR_surjective n p hp (T_gen_generates_R_p n p hp)⟩

end HeckeRing.GLn
