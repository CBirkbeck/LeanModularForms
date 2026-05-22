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

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset Matrix.SpecialLinearGroup

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
  ⟨MvPolynomial.X k, by simp [evalHom, MvPolynomial.eval₂Hom_X']⟩

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
  ⟨MvPolynomial.X 0, by simp [evalHom, MvPolynomial.eval₂Hom_X']⟩

private lemma X_one_mem_range (p : ℕ) :
    T_gen 2 p (1 : Fin 2) ∈ (evalHom 2 p).range :=
  ⟨MvPolynomial.X 1, by simp [evalHom, MvPolynomial.eval₂Hom_X']⟩

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
    show evalHom n p (MvPolynomial.C a) ∈ R_p n p hp
    simp only [evalHom, MvPolynomial.eval₂Hom_C]
    show (a : HeckeAlgebra n) ∈ R_p n p hp
    rw [show (a : HeckeAlgebra n) = a • (1 : HeckeAlgebra n) from (zsmul_one a).symm]
    exact (R_p n p hp).zsmul_mem (R_p n p hp).one_mem a
  · intro f g hf hg; rw [map_add]; exact (R_p n p hp).add_mem hf hg
  · intro f i hf
    rw [map_mul]
    exact (R_p n p hp).mul_mem hf (by
      show evalHom n p (MvPolynomial.X i) ∈ R_p n p hp
      simp only [evalHom, MvPolynomial.eval₂Hom_X']
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
  show Finsupp.toFun (MvPolynomial.eval₂Hom (Int.castRingHom (HeckeAlgebra 1))
    (fun k => T_gen 1 p k) R) D = _
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', Fin.prod_univ_one,
    T_gen_pow_one p hp]
  -- Rewrite each summand: (intCast (coeff x R)) * T_elem (fun _ => p^x 0)
  --   = Finsupp.single (T_diag fun _ => p^x 0) (coeff x R)
  have hsum : ∀ x : Fin 1 →₀ ℕ,
      ((Int.castRingHom (HeckeAlgebra 1)) (MvPolynomial.coeff x R) *
        T_elem (n := 1) (fun _ ↦ p ^ x 0)) =
      (Finsupp.single (T_diag (n := 1) (fun _ ↦ p ^ x 0)) (MvPolynomial.coeff x R) :
        HeckeAlgebra 1) := by
    intro x
    unfold T_elem
    -- (n : HeckeAlgebra) * Finsupp.single d 1 = Finsupp.single d n via zsmul
    rw [show ((Int.castRingHom (HeckeAlgebra 1)) (MvPolynomial.coeff x R)) =
        (MvPolynomial.coeff x R) • (1 : HeckeAlgebra 1) from by
      rw [zsmul_eq_mul, mul_one]; rfl,
      smul_mul_assoc, one_mul]
    show (MvPolynomial.coeff x R) •
        (Finsupp.single (T_diag (n := 1) (fun _ ↦ p ^ x 0)) (1 : ℤ) :
          HeckeCoset (GL_pair 1) →₀ ℤ) =
      Finsupp.single (T_diag (n := 1) (fun _ ↦ p ^ x 0)) (MvPolynomial.coeff x R)
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl (fun x _ => hsum x)]
  -- Now push .toFun through the sum (it's a Finsupp; .toFun = coe)
  show ((∑ x ∈ R.support,
      (Finsupp.single (T_diag (n := 1) (fun _ ↦ p ^ x 0))
        (MvPolynomial.coeff x R) : HeckeCoset (GL_pair 1) →₀ ℤ))) D =
    MvPolynomial.coeff s R
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, D]
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hbs
    apply if_neg
    intro hb
    apply hbs
    have ha_pos : ∀ _ : Fin 1, 0 < p ^ b 0 :=
      fun _ => Nat.pow_pos hp.pos
    have hb_pos : ∀ _ : Fin 1, 0 < p ^ s 0 :=
      fun _ => Nat.pow_pos hp.pos
    have hda : DivChain 1 (fun _ : Fin 1 => p ^ b 0) := by
      intro i hi; exact absurd hi (by omega)
    have hdb : DivChain 1 (fun _ : Fin 1 => p ^ s 0) := by
      intro i hi; exact absurd hi (by omega)
    have heq := diagonal_representative_unique (n := 1) _ _ ha_pos hb_pos hda hdb hb
    have h0 : p ^ b 0 = p ^ s 0 := congr_fun heq 0
    have hbs0 : b 0 = s 0 := Nat.pow_right_injective hp.two_le h0
    refine Finsupp.ext (fun j => ?_)
    have hj : j = 0 := Fin.fin_one_eq_zero j
    rw [hj]; exact hbs0
  · intro hns
    exact absurd hs hns

/-! #### n=2 injectivity -/

/-! ##### Det/support helpers -/

/-- Determinant of an SL_n(ℤ) element embedded in GL_n(ℚ) is 1. -/
lemma det_SLnZ_eq_one {g : GL (Fin 2) ℚ} (hg : g ∈ SLnZ_subgroup 2) :
    (↑g : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
  obtain ⟨σ, rfl⟩ := hg; simp [mapGL, det_intMat_cast, SpecialLinearGroup.det_coe]

/-- Elements in the same SL_n double coset have the same determinant. -/
lemma det_doubleCoset_eq {g₁ g₂ : (GL_pair 2).Δ}
    (h : (⟦g₁⟧ : HeckeCoset (GL_pair 2)) = ⟦g₂⟧) :
    (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
    (↑(↑g₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rw [HeckeCoset.eq_iff] at h
  have hg₁_mem : (g₁ : GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (g₂ : GL (Fin 2) ℚ) (GL_pair 2).H (GL_pair 2).H := by
    rw [← h]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := DoubleCoset.mem_doubleCoset.mp hg₁_mem
  have : (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (h₁ * (↑g₂ : GL (Fin 2) ℚ) * h₂).1.det := by rw [heq]
  simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul,
    det_SLnZ_eq_one hh₁, det_SLnZ_eq_one hh₂, one_mul, mul_one] at this
  exact this

/-- The diagonal product of rep(T_diag a) equals ∏ a. -/
lemma prod_rep_T_diag (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(↑(HeckeCoset.rep (T_diag a)) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
    ∏ i, (a i : ℚ) := by
  have h_eq : (⟦HeckeCoset.rep (T_diag a)⟧ : HeckeCoset (GL_pair 2)) = T_diag a :=
    Quotient.out_eq _
  rw [show T_diag a = (⟦diagMat_delta 2 a⟧ : HeckeCoset (GL_pair 2)) from rfl] at h_eq
  exact (det_doubleCoset_eq h_eq).trans (by simp [diagMat_delta_val 2 a ha, diagMat_det 2 a ha])

/-- Every coset in the support of a mulMap output has determinant = det(g₁) * det(g₂). -/
lemma det_mulMap_eq (g₁ g₂ : (GL_pair 2).Δ)
    (p : HeckeRing.decompQuot (GL_pair 2) g₁ × HeckeRing.decompQuot (GL_pair 2) g₂) :
    (↑(↑(HeckeCoset.rep (HeckeRing.mulMap (GL_pair 2) g₁ g₂ p)) : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ).det =
    (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det *
    (↑(↑g₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  -- mulMap output = ⟦σ * g₁ * (τ * g₂)⟧ for σ, τ ∈ SL_n
  -- rep is in the same double coset, so has the same det
  have h_eq : (⟦HeckeCoset.rep (HeckeRing.mulMap (GL_pair 2) g₁ g₂ p)⟧ :
      HeckeCoset (GL_pair 2)) = HeckeRing.mulMap (GL_pair 2) g₁ g₂ p := Quotient.out_eq _
  rw [det_doubleCoset_eq h_eq]
  -- Now goal: det of the unfolded mulMap element = det(g₁) * det(g₂)
  -- The mulMap element is ⟨p.1.out * g₁ * (p.2.out * g₂), _⟩ with coe into GL
  show (((p.1.out : GL (Fin 2) ℚ) * (g₁ : GL (Fin 2) ℚ) *
      ((p.2.out : GL (Fin 2) ℚ) * (g₂ : GL (Fin 2) ℚ)) :
      GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = _
  simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul]
  have h1 := det_SLnZ_eq_one (p.1.out.2)
  have h2 := det_SLnZ_eq_one (p.2.out.2)
  rw [h1, h2]; ring

lemma T_gen_pow_support_qpower (q : {p : ℕ // p.Prime})
    (e : Fin 2 → ℕ) (D : HeckeCoset (GL_pair 2))
    (hD : (T_gen 2 q.1 0 ^ (e 0) * T_gen 2 q.1 1 ^ (e 1)) D ≠ 0) :
    ∃ a : Fin 2 → ℕ, D = T_diag a ∧ (∀ i, 0 < a i) ∧ DivChain 2 a ∧
      (∏ i, a i) = q.1 ^ (e 0 + 2 * e 1) := by
  -- D is a Hecke coset, so has a diagonal representative
  obtain ⟨a, ha_pos, ha_div, ha_eq⟩ := exists_diagonal_representative 2 (HeckeCoset.rep D)
  have hD_eq : D = T_diag a := by rw [← Quotient.out_eq D]; exact ha_eq
  refine ⟨a, hD_eq, ha_pos, ha_div, ?_⟩
  -- Show ∏ a = q^{e 0 + 2*e 1} by determinant tracking
  -- Every support coset has det = q^{e 0} * q^{2*e 1} = q^{e 0 + 2*e 1}
  suffices h_det : ∀ (a₀ b₀ : ℕ) (f : HeckeAlgebra 2) (D' : HeckeCoset (GL_pair 2)),
      (∀ D'', f D'' ≠ 0 →
        (↑(↑(HeckeCoset.rep D'') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
        ↑(q.1 ^ a₀ : ℕ)) →
      (T_gen 2 q.1 0 ^ b₀ * f) D' ≠ 0 →
      (↑(↑(HeckeCoset.rep D') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
        ↑(q.1 ^ (b₀ + a₀) : ℕ) by
    -- Apply h_det with f = T_gen(q,1)^{e 1}, a₀ = 2*e 1, b₀ = e 0
    have hf_det : ∀ D'', (T_gen 2 q.1 1 ^ (e 1)) D'' ≠ 0 →
        (↑(↑(HeckeCoset.rep D'') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
        ↑(q.1 ^ (2 * e 1) : ℕ) := by
      intro D'' hD''
      -- T_gen(q,1)^{e 1} = T_elem(![q^{e 1}, q^{e 1}]) = single(T_diag(...), 1)
      rw [show T_gen 2 q.1 1 = HeckeRing.GL2.T_pp q.1 from
          HeckeRing.GLn.Surj.T_gen_one_eq_T_pp q.1 q.2,
        HeckeRing.GL2.T_pp_pow q.1 q.2 (e 1)] at hD''
      have h_eq : T_diag (fun _ : Fin 2 => q.1 ^ (e 1)) = D'' := by
        by_contra h
        apply hD''
        show (Finsupp.single (T_diag (fun _ : Fin 2 => q.1 ^ (e 1))) (1 : ℤ)) D'' = 0
        rw [Finsupp.single_apply, if_neg h]
      rw [← h_eq]
      rw [prod_rep_T_diag _ (fun i => by fin_cases i <;> simp [pow_pos q.2.pos])]
      push_cast [Fin.prod_univ_two, ← pow_add]
      ring_nf
    have h_result := h_det (2 * e 1) (e 0) (T_gen 2 q.1 1 ^ (e 1)) D hf_det hD
    rw [hD_eq, prod_rep_T_diag a ha_pos] at h_result
    rw [show e 0 + 2 * e 1 = e 0 + (2 * e 1) from by ring] at h_result
    -- h_result : ∏ (a i : ℚ) = ↑(q.1 ^ (e 0 + 2 * e 1))
    exact_mod_cast h_result
  -- Prove h_det by induction on b₀
  intro a₀; intro b₀; induction b₀ with
  | zero =>
    intro f D' hf_det hD'
    simp only [pow_zero, one_mul, Nat.zero_add] at hD' ⊢
    exact hf_det D' hD'
  | succ n ih =>
    intro f D' hf_det hD'
    rw [pow_succ', mul_assoc] at hD'
    -- hD' : (T_gen(q,0) * (T_gen(q,0)^n * f)) D' ≠ 0
    set g' := T_gen 2 q.1 0 ^ n * f with hg'_def
    -- T_gen(q,0) = T_elem(![1,q]) = single(T_diag(![1,q]), 1)
    set D₁ := T_diag (![1, q.1]) with hD₁_def
    have hf_eq : T_gen 2 q.1 0 = HeckeRing.T_single (GL_pair 2) ℤ D₁ 1 := by
      show T_elem (T_gen_diag 2 q.1 0) = _; congr 1
      funext i; simp [T_gen_diag]; fin_cases i <;> simp
    rw [hf_eq] at hD'
    -- Expand (single D₁ 1 * g')(D') as sum
    have h_expand : (HeckeRing.T_single (GL_pair 2) ℤ D₁ 1 * g') D' =
        g'.sum (fun D₂ c₂ => c₂ * (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
          (HeckeCoset.rep D₂)) D') := by
      show (Finsupp.sum (Finsupp.single D₁ 1)
        (fun D₁' b₁ => g'.sum (fun D₂ b₂ =>
          b₁ • b₂ • HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁') (HeckeCoset.rep D₂)))) D' = _
      rw [Finsupp.sum_single_index (by simp [Finsupp.sum])]
      simp [Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [h_expand] at hD'
    -- Extract D₂ with nonzero contribution
    rw [Finsupp.sum] at hD'
    obtain ⟨D₂, hD₂_mem, hD₂_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hD'
    have hgD₂ : g' D₂ ≠ 0 := Finsupp.mem_support_iff.mp hD₂_mem
    have hm_ne : (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D' ≠ 0 := by
      intro h; exact hD₂_ne (by rw [h, mul_zero])
    -- D' ∈ mulSupport(rep D₁, rep D₂)
    rw [HeckeRing.m_apply] at hm_ne
    have hD'_mem : D' ∈ HeckeRing.mulSupport (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) := by
      rw [← HeckeRing.m_support]; exact Finsupp.mem_support_iff.mpr hm_ne
    -- D' = mulMap(...)(p) for some p
    rw [HeckeRing.mulSupport, Finset.mem_image] at hD'_mem
    obtain ⟨p, _, hD'_eq⟩ := hD'_mem
    -- det(rep D') = det(rep D₁) * det(rep D₂)
    have h_det_D' := det_mulMap_eq (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) p
    rw [hD'_eq] at h_det_D'
    -- det(rep D₁) = q (from prod_rep_T_diag)
    have h_det_D₁ : (↑(↑(HeckeCoset.rep D₁) : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ).det = (q.1 : ℚ) := by
      rw [prod_rep_T_diag (![1, q.1]) (fun i => by fin_cases i <;> simp [q.2.pos])]
      simp [Fin.prod_univ_two]
    -- det(rep D₂) = q^{n+a₀} by IH
    have h_det_D₂ : (↑(↑(HeckeCoset.rep D₂) : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ).det = ↑(q.1 ^ (n + a₀) : ℕ) :=
      ih f D₂ hf_det hgD₂
    -- Combine: det(rep D') = q^{n+1+a₀}
    rw [h_det_D₁, h_det_D₂] at h_det_D'
    convert h_det_D' using 1
    push_cast; ring

/-- Every coset in the support of `T_gen(q,0)^a * T_gen(q,1)^b` has entries
that are powers of `q` (immediate from `T_gen_pow_support_qpower`). -/
lemma T_gen_pow_entries_qpower (q : {p : ℕ // p.Prime})
    (e : Fin 2 → ℕ) (D : HeckeCoset (GL_pair 2))
    (hD : (T_gen 2 q.1 0 ^ (e 0) * T_gen 2 q.1 1 ^ (e 1)) D ≠ 0)
    (a : Fin 2 → ℕ) (ha : D = T_diag a) (ha_pos : ∀ i, 0 < a i)
    (ha_div : DivChain 2 a) :
    ∀ p : ℕ, p.Prime → p ≠ q.1 → ∀ i, ¬(p ∣ a i) := by
  obtain ⟨a', rfl, ha'_pos, ha'_div, ha'_det⟩ := T_gen_pow_support_qpower q e D hD
  have ha_eq := diagonal_representative_unique 2 a a' ha_pos ha'_pos ha_div ha'_div ha.symm
  subst ha_eq
  intro p hp hpq i
  intro h_dvd
  have : p ∣ ∏ j, a j := dvd_trans h_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  rw [ha'_det] at this
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.2).mp (hp.dvd_of_dvd_pow this))

/-- If `(f * g)(D) ≠ 0` in the Hecke ring, there exist `D₁ ∈ supp(f)` and `D₂ ∈ supp(g)`
with `D ∈ mulSupport(rep D₁, rep D₂)`. -/
lemma support_mul_exists (f g : HeckeAlgebra 2) (D : HeckeCoset (GL_pair 2))
    (hD : (f * g) D ≠ 0) :
    ∃ D₁ D₂, f D₁ ≠ 0 ∧ g D₂ ≠ 0 ∧
      D ∈ HeckeRing.mulSupport (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) := by
  -- Expand f * g using mul_def
  have h : (Finsupp.sum f (fun D₁ b₁ => Finsupp.sum g (fun D₂ b₂ =>
      b₁ • b₂ • HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂)))) D ≠ 0 := hD
  simp only [Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at h
  obtain ⟨D₁, hD₁_mem, h₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨D₂, hD₂_mem, h₂⟩ := Finset.exists_ne_zero_of_sum_ne_zero h₁
  have hfD₁ := Finsupp.mem_support_iff.mp hD₁_mem
  have hgD₂ := Finsupp.mem_support_iff.mp hD₂_mem
  have hm_ne : (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D ≠ 0 := by
    intro h; exact h₂ (by rw [h, mul_zero, mul_zero])
  refine ⟨D₁, D₂, hfD₁, hgD₂, ?_⟩
  rw [← HeckeRing.m_support]
  exact Finsupp.mem_support_iff.mpr hm_ne

/-! ##### Kronecker delta infrastructure -/

/-- Helper: `T_single(T_diag a, α) * T_elem(c,c) = T_single(T_diag(a * c), α)`.
Immediate consequence of `T_elem_mul_scalar`. -/
lemma T_single_diag_mul_T_scalar (c : ℕ) (hc : 0 < c)
    (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i) (ha_div : DivChain 2 a) (α : ℤ) :
    HeckeRing.T_single (GL_pair 2) ℤ (T_diag a) α * T_elem (fun _ : Fin 2 => c) =
    HeckeRing.T_single (GL_pair 2) ℤ (T_diag (a * (fun _ : Fin 2 => c))) α := by
  have h_single : HeckeRing.T_single (GL_pair 2) ℤ (T_diag a) α =
      α • T_elem a := by
    show HeckeRing.T_single (GL_pair 2) ℤ (T_diag a) α =
         α • HeckeRing.T_single (GL_pair 2) ℤ (T_diag a) 1
    rw [HeckeRing.T_single_smul]; congr 1; ring
  rw [h_single, smul_mul_assoc, T_elem_mul_scalar a ha_pos ha_div c hc]
  show α • HeckeRing.T_single (GL_pair 2) ℤ (T_diag (a * fun _ => c)) 1 = _
  rw [HeckeRing.T_single_smul]; congr 1; ring

/-- **Scalar shift identity (matching target)**: For any `f : HeckeAlgebra 2`, any scalar
`c > 0`, and any positive divisibility-chain `b`, the evaluation of `f * T_elem(c,c)` at
the scaled diagonal `T_diag(b * c)` equals `f(T_diag b)`.

This is the key structural lemma: right-multiplication by a scalar-diagonal element
shifts the support by the scalar, preserving coefficients. -/
lemma T_mul_T_scalar_eval_shifted (c : ℕ) (hc : 0 < c)
    (f : HeckeAlgebra 2) (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i) (hb_div : DivChain 2 b) :
    (f * T_elem (fun _ : Fin 2 => c)) (T_diag (b * (fun _ : Fin 2 => c))) = f (T_diag b) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    show ((0 : HeckeAlgebra 2) * T_elem (fun _ : Fin 2 => c)) (T_diag (b * fun _ => c)) =
         (0 : HeckeAlgebra 2) (T_diag b)
    rw [zero_mul]; rfl
  | add g h ihg ihh => rw [add_mul, Finsupp.add_apply, Finsupp.add_apply, ihg, ihh]
  | single D α =>
    obtain ⟨a, ha_pos, ha_div, ha_eq⟩ := exists_diagonal_representative 2 (HeckeCoset.rep D)
    have hD_eq : D = T_diag a := by rw [← Quotient.out_eq D]; exact ha_eq
    change (HeckeRing.T_single (GL_pair 2) ℤ D α * T_elem (fun _ : Fin 2 => c))
             (T_diag (b * fun _ : Fin 2 => c)) =
           HeckeRing.T_single (GL_pair 2) ℤ D α (T_diag b)
    rw [hD_eq, T_single_diag_mul_T_scalar c hc a ha_pos ha_div α]
    -- Goal: T_single(T_diag(a*c), α)(T_diag(b*c)) = T_single(T_diag a, α)(T_diag b)
    show Finsupp.single (T_diag (a * fun _ : Fin 2 => c)) α (T_diag (b * fun _ : Fin 2 => c)) =
         Finsupp.single (T_diag a) α (T_diag b)
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl, if_pos rfl]
    · have h_ne_1 : T_diag (a * fun _ : Fin 2 => c) ≠ T_diag (b * fun _ : Fin 2 => c) := by
        intro heq
        have h1_eq : a * (fun _ : Fin 2 => c) = b * (fun _ : Fin 2 => c) :=
          diagonal_representative_unique 2 _ _
            (fun i => Nat.mul_pos (ha_pos i) hc)
            (fun i => Nat.mul_pos (hb_pos i) hc)
            (DivChain_mul 2 a _ ha_div (divChain_const 2 c))
            (DivChain_mul 2 b _ hb_div (divChain_const 2 c))
            heq
        apply hab
        funext i
        have := congr_fun h1_eq i
        simp only [Pi.mul_apply] at this
        exact Nat.eq_of_mul_eq_mul_right hc this
      have h_ne_2 : T_diag a ≠ T_diag b := fun heq => hab
        (diagonal_representative_unique 2 a b ha_pos hb_pos ha_div hb_div heq)
      rw [if_neg h_ne_1, if_neg h_ne_2]

/-- **Scalar shift zero direction**: If `c ∤ d i` for some `i`, the evaluation of
`f * T_elem(c,c)` at `T_diag d` is zero. -/
lemma T_mul_T_scalar_eval_zero_of_not_dvd (c : ℕ) (hc : 0 < c)
    (f : HeckeAlgebra 2) (d : Fin 2 → ℕ) (hd_pos : ∀ i, 0 < d i) (hd_div : DivChain 2 d)
    (i₀ : Fin 2) (hi₀ : ¬ c ∣ d i₀) :
    (f * T_elem (fun _ : Fin 2 => c)) (T_diag d) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero =>
    show ((0 : HeckeAlgebra 2) * T_elem (fun _ : Fin 2 => c)) (T_diag d) = 0
    rw [zero_mul]; rfl
  | add g h ihg ihh => rw [add_mul, Finsupp.add_apply, ihg, ihh, add_zero]
  | single D α =>
    obtain ⟨a, ha_pos, ha_div, ha_eq⟩ := exists_diagonal_representative 2 (HeckeCoset.rep D)
    have hD_eq : D = T_diag a := by rw [← Quotient.out_eq D]; exact ha_eq
    change (HeckeRing.T_single (GL_pair 2) ℤ D α * T_elem (fun _ : Fin 2 => c)) (T_diag d) = 0
    rw [hD_eq, T_single_diag_mul_T_scalar c hc a ha_pos ha_div α]
    show Finsupp.single (T_diag (a * fun _ : Fin 2 => c)) α (T_diag d) = 0
    rw [Finsupp.single_apply]
    have h_ne : T_diag (a * fun _ : Fin 2 => c) ≠ T_diag d := by
      intro heq
      have h_eq : a * (fun _ : Fin 2 => c) = d :=
        diagonal_representative_unique 2 _ d
          (fun i => Nat.mul_pos (ha_pos i) hc) hd_pos
          (DivChain_mul 2 a _ ha_div (divChain_const 2 c))
          hd_div heq
      apply hi₀
      have := congr_fun h_eq i₀
      simp only [Pi.mul_apply] at this
      exact ⟨a i₀, by linarith [this.symm]⟩
    rw [if_neg h_ne]

/-- Helper: For `i ≥ 1`, evaluation of `f * T_pp(p)^i` at `T_diag ![1, k]` is zero
(since `p^i ∤ 1`). -/
lemma T_mul_T_pp_pow_eval_at_one_zero (p : ℕ) (hp : p.Prime) (i k : ℕ) (hi : 1 ≤ i)
    (hk : 0 < k) (f : HeckeAlgebra 2) :
    (f * T_pp p ^ i) (T_diag (![1, k] : Fin 2 → ℕ)) = 0 := by
  rw [HeckeRing.GL2.T_pp_pow p hp i]
  apply T_mul_T_scalar_eval_zero_of_not_dvd (p^i) (pow_pos hp.pos i) f
    (![1, k] : Fin 2 → ℕ) (fun idx => by fin_cases idx <;> simp [hk])
    (fun j hj => by
      have : j = 0 := by omega
      subst this; simp) 0
  simp only [Matrix.cons_val_zero]
  intro hdvd
  have hle : p ^ i ≤ 1 := Nat.le_of_dvd Nat.one_pos hdvd
  have hge : p ≤ p ^ i := Nat.le_self_pow (by omega) p
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- Helper: `T_elem ![p^i, p^j] = T_ad(1, p^{j-i}) * T_pp(p)^i` for `i ≤ j` with `p` prime.
Factors out the scalar `p^i` from both entries. -/
lemma T_elem_ppow_factor (p : ℕ) (hp : p.Prime) (i j : ℕ) (hij : i ≤ j) :
    T_elem (![p^i, p^j] : Fin 2 → ℕ) = T_ad 1 (p ^ (j - i)) * T_pp p ^ i := by
  rw [T_ad_of_pos 1 (p^(j-i)) Nat.one_pos (pow_pos hp.pos _) (one_dvd _),
      HeckeRing.GL2.T_pp_pow p hp i]
  have h_ji_pos : ∀ idx : Fin 2, 0 < (![1, p^(j-i)] : Fin 2 → ℕ) idx := by
    intro idx; fin_cases idx
    · simp
    · simp [pow_pos hp.pos]
  have h_ji_div : DivChain 2 (![1, p^(j-i)] : Fin 2 → ℕ) := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0; simp
  rw [T_elem_mul_scalar (![1, p^(j-i)] : Fin 2 → ℕ) h_ji_pos h_ji_div (p^i) (pow_pos hp.pos _)]
  apply T_elem_congr_diag
  funext idx; fin_cases idx
  · simp [Pi.mul_apply]
  · simp [Pi.mul_apply, ← pow_add]; congr 1; omega

/-- **Leading coefficient of `T(1,p)^a`**: `(T_ad 1 p)^a` evaluated at the leading
coset `T_diag ![1, p^a]` equals 1.

**Proof by induction on `a`** using Shimura's recurrence `T(p) * T(1, p^k) = T(1, p^{k+1}) +
m_k * T(p, p^k)`. The key fact is that for `i ≥ 1`, any support element `T(p^i, p^{a-i})` in
`T(1,p)^a` contributes 0 at `T(1, p^{a+1})` since the product factors through `T_pp(p)^i`
which scales entries by `p^i`, and `p^i ∤ 1`. Only the `i = 0` leading term `T(1, p^a)`
contributes coefficient 1. -/
lemma T_ad_one_p_pow_eval_leading (p : ℕ) (hp : p.Prime) (a : ℕ) :
    ((T_ad 1 p) ^ a) (T_diag (![1, p ^ a] : Fin 2 → ℕ)) = 1 := by
  induction a with
  | zero =>
    -- (T_ad 1 p)^0 = 1, target = T_diag ![1, p^0] = T_diag ![1, 1] = HeckeCoset.one
    show ((T_ad 1 p) ^ 0) (T_diag (![1, p ^ 0] : Fin 2 → ℕ)) = 1
    rw [pow_zero, pow_zero]
    show (1 : HeckeAlgebra 2) (T_diag (![1, 1] : Fin 2 → ℕ)) = 1
    rw [HeckeRing.one_def]
    show Finsupp.single (HeckeCoset.one (GL_pair 2)) (1 : ℤ)
         (T_diag (![1, 1] : Fin 2 → ℕ)) = 1
    have h_target : (T_diag (![1, 1] : Fin 2 → ℕ) : HeckeCoset (GL_pair 2)) =
                    HeckeCoset.one (GL_pair 2) := by
      rw [show (![1, 1] : Fin 2 → ℕ) = (fun _ : Fin 2 => 1) from by
            funext i; fin_cases i <;> rfl]
      exact T_diag_ones
    rw [h_target, Finsupp.single_eq_same]
  | succ n ih =>
    -- (T_ad 1 p)^(n+1) = T_ad(1,p) * (T_ad 1 p)^n
    -- The mul_def expansion:
    -- ((T_ad 1 p) * (T_ad 1 p)^n) (T_diag ![1, p^(n+1)])
    --   = Σ_{D₂ ∈ supp((T_ad 1 p)^n)} (T_ad 1 p)^n(D₂) *
    --         m(rep T_diag ![1,p], rep D₂)(T_diag ![1, p^(n+1)])
    -- Only D₂ = T_diag ![1, p^n] (from i=0) contributes; use Shimura 3.24(5).
    rw [pow_succ']
    -- Set up
    set g := (T_ad 1 p) ^ n
    set D_target : HeckeCoset (GL_pair 2) := T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)
    set D_leading : HeckeCoset (GL_pair 2) := T_diag (![1, p ^ n] : Fin 2 → ℕ)
    -- Step 1: the product T_ad 1 p * T_single(D, 1) for D = T_diag ![p^i, p^{n-i}]
    -- in supp(g) at D_target is either 1 (when i=0, D = D_leading) or 0 (when i ≥ 1).
    -- Extract this via a Finset.sum decomposition on g.support.
    -- First, express the multiplication as a Finsupp sum.
    rw [show T_ad 1 p = HeckeRing.T_single (GL_pair 2) ℤ (T_diag (![1, p] : Fin 2 → ℕ)) 1 from
        T_ad_of_pos 1 p Nat.one_pos hp.pos (one_dvd _)]
    -- Use HeckeRing.mul_def and Finsupp.sum_single_index for the outer sum
    rw [HeckeRing.mul_def]
    rw [Finsupp.sum_single_index (by simp [Finsupp.sum])]
    -- Now: (1 • g.sum (fun D₂ b₂ => 1 • b₂ • m(rep T_diag ![1,p], rep D₂))) D_target
    simp only [one_smul]
    rw [Finsupp.sum_apply]
    -- Split the sum into: D_leading (if in supp) and others
    -- The term at D_leading = T_diag ![1, p^n] gives 1 * 1 = 1 (by Shimura); others give 0.
    have h_leading_mult : (HeckeRing.m (GL_pair 2) (HeckeCoset.rep (T_diag (![1, p] : Fin 2 → ℕ)))
          (HeckeCoset.rep D_leading)) D_target = 1 := by
      -- m(rep T_diag ![1,p], rep T_diag ![1,p^n]) = T_single(T_diag ![1,p], 1) * T_single(T_diag ![1,p^n], 1)
      rw [← HeckeRing.T_single_one_mul_T_single_one]
      change (T_elem (![1, p] : Fin 2 → ℕ) * T_elem (![1, p ^ n] : Fin 2 → ℕ)) D_target = 1
      rw [show T_elem (![1, p] : Fin 2 → ℕ) = T_ad 1 p from
          (T_ad_of_pos 1 p Nat.one_pos hp.pos (one_dvd _)).symm,
         show T_elem (![1, p ^ n] : Fin 2 → ℕ) = T_ad 1 (p ^ n) from
          (T_ad_of_pos 1 (p ^ n) Nat.one_pos (pow_pos hp.pos n) (one_dvd _)).symm]
      by_cases hn : n = 0
      · subst hn
        rw [pow_zero, T_ad_one_one, mul_one]
        show T_ad 1 p D_target = 1
        simp only [D_target]
        rw [T_ad_of_pos 1 p Nat.one_pos hp.pos (one_dvd _)]
        show (Finsupp.single (T_diag (![1, p] : Fin 2 → ℕ)) (1 : ℤ))
             (T_diag (![1, p ^ (0 + 1)] : Fin 2 → ℕ)) = 1
        rw [show (![1, p ^ (0 + 1)] : Fin 2 → ℕ) = (![1, p] : Fin 2 → ℕ) from by
            funext i; fin_cases i <;> simp]
        exact Finsupp.single_eq_same
      · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
        rw [show T_ad 1 p = T_sum ⟨p, hp.pos⟩ from (T_sum_prime p hp).symm]
        rw [T_sum_prime_mul_T_ad p hp n hn_pos]
        rw [Finsupp.add_apply]
        rw [T_ad_of_pos 1 (p ^ (n + 1)) Nat.one_pos (pow_pos hp.pos _) (one_dvd _)]
        rw [T_ad_of_pos p (p ^ n) hp.pos (pow_pos hp.pos _)
            (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn_pos))]
        simp only [D_target]
        rw [show (T_elem (![1, p ^ (n + 1)] : Fin 2 → ℕ))
              (T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 1 from by
            show (Finsupp.single (T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)) (1 : ℤ)) _ = 1
            exact Finsupp.single_eq_same]
        have h_Telem_zero : (T_elem (![p, p ^ n] : Fin 2 → ℕ))
              (T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 0 := by
          show (Finsupp.single (T_diag (![p, p ^ n] : Fin 2 → ℕ)) (1 : ℤ)) _ = 0
          apply Finsupp.single_eq_of_ne'
          intro heq
          have hpp_pos : ∀ i : Fin 2, 0 < (![p, p ^ n] : Fin 2 → ℕ) i := fun i => by
            fin_cases i <;> simp [hp.pos, pow_pos hp.pos]
          have h1pn_pos : ∀ i : Fin 2, 0 < (![1, p ^ (n + 1)] : Fin 2 → ℕ) i := fun i => by
            fin_cases i <;> simp [pow_pos hp.pos]
          have hpp_div : DivChain 2 (![p, p ^ n] : Fin 2 → ℕ) := fun j hj => by
            have hj0 : j = 0 := by omega
            subst hj0
            show (![p, p ^ n] : Fin 2 → ℕ) ⟨0, _⟩ ∣ (![p, p ^ n] : Fin 2 → ℕ) ⟨0 + 1, _⟩
            show p ∣ p ^ n
            exact dvd_pow_self p hn
          have h1pn_div : DivChain 2 (![1, p ^ (n + 1)] : Fin 2 → ℕ) := fun j hj => by
            have hj0 : j = 0 := by omega
            subst hj0
            show (![1, p ^ (n + 1)] : Fin 2 → ℕ) ⟨0, _⟩ ∣
                 (![1, p ^ (n + 1)] : Fin 2 → ℕ) ⟨0 + 1, _⟩
            exact one_dvd _
          have h_eq : (![p, p ^ n] : Fin 2 → ℕ) = (![1, p ^ (n + 1)] : Fin 2 → ℕ) :=
            diagonal_representative_unique 2 _ _ hpp_pos h1pn_pos hpp_div h1pn_div heq
          have := congr_fun h_eq 0
          simp only [Matrix.cons_val_zero] at this
          have := hp.one_lt; omega
        rw [Finsupp.smul_apply, h_Telem_zero, smul_zero, add_zero]
    have h_non_leading_mult : ∀ (D₂ : HeckeCoset (GL_pair 2)), D₂ ∈ g.support →
        D₂ ≠ D_leading →
        (HeckeRing.m (GL_pair 2) (HeckeCoset.rep (T_diag (![1, p] : Fin 2 → ℕ)))
          (HeckeCoset.rep D₂)) D_target = 0 := by
      intro D₂ hD₂_supp hD₂_ne
      have hD₂_ne_zero : g D₂ ≠ 0 := Finsupp.mem_support_iff.mp hD₂_supp
      -- Rewrite g D₂ in the form of T_gen_pow_support_qpower
      have hg_eq : g = (T_gen 2 p 0) ^ n * (T_gen 2 p 1) ^ 0 := by
        simp only [pow_zero, mul_one]
        show (T_ad 1 p) ^ n = (T_gen 2 p 0) ^ n
        rw [HeckeRing.GLn.Surj.T_gen_zero_eq_T_ad p hp]
      obtain ⟨a, hDa, ha_pos, ha_div, ha_det⟩ := T_gen_pow_support_qpower ⟨p, hp⟩
          ![n, 0] D₂ (hg_eq ▸ hD₂_ne_zero)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_zero,
        add_zero] at ha_det
      -- Extract i : a 0 = p^i from Nat.dvd_prime_pow (a 0 ∣ p^n).
      have ha0_dvd : a 0 ∣ p ^ n := ha_det ▸ Fin.prod_univ_two a ▸ dvd_mul_right _ _
      obtain ⟨i, hi_le, hi_eq⟩ := (Nat.dvd_prime_pow hp).mp ha0_dvd
      -- Similarly, a 1 = p^j with j = n - i (since a 0 * a 1 = p^n).
      have ha1_eq : a 1 = p ^ (n - i) := by
        have : a 0 * a 1 = p ^ n := Fin.prod_univ_two a ▸ ha_det
        rw [hi_eq] at this
        have h_can : p ^ i * a 1 = p ^ i * p ^ (n - i) := by
          rw [this, ← pow_add]; congr 1; omega
        exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i) h_can
      -- Now D₂ = T_diag ![p^i, p^{n-i}]. Since D₂ ≠ D_leading = T_diag ![1, p^n], i ≥ 1.
      have ha_form : a = (![p ^ i, p ^ (n - i)] : Fin 2 → ℕ) := by
        funext k; fin_cases k
        · exact hi_eq
        · exact ha1_eq
      have hi_ge : 1 ≤ i := by
        by_contra h_not
        push_neg at h_not
        have hi0 : i = 0 := by omega
        apply hD₂_ne
        rw [hDa, ha_form, hi0]
        show (T_diag (![p^0, p^(n-0)] : Fin 2 → ℕ)) = _
        show T_diag ![1, p ^ n] = D_leading
        simp [D_leading, pow_zero]
      -- Multiplicity = (T_elem ![1, p] * T_elem ![p^i, p^(n-i)]) D_target
      -- Factor T_elem ![p^i, p^(n-i)] = T_ad(1, p^(n-2i)) * T_pp p^i
      -- Use T_mul_T_pp_pow_eval_at_one_zero
      rw [hDa, ha_form, ← HeckeRing.T_single_one_mul_T_single_one]
      change (T_elem (![1, p] : Fin 2 → ℕ) * T_elem (![p^i, p^(n-i)] : Fin 2 → ℕ)) D_target = 0
      -- Need i ≤ n - i (from DivChain)
      have hi_le_sub : i ≤ n - i := by
        have h_div_01 := ha_div 0 (by omega : 0 + 1 < 2)
        rw [ha_form] at h_div_01
        have h_pow_dvd : p ^ i ∣ p ^ (n - i) := h_div_01
        rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h_pow_dvd
        exact h_pow_dvd
      rw [T_elem_ppow_factor p hp i (n - i) hi_le_sub]
      rw [← mul_assoc]
      exact T_mul_T_pp_pow_eval_at_one_zero p hp i (p ^ (n + 1)) hi_ge
        (pow_pos hp.pos _) _
    -- Use h_leading_mult and h_non_leading_mult to conclude the sum is 1
    rw [Finsupp.sum]
    have h_leading_in_supp : D_leading ∈ g.support :=
      Finsupp.mem_support_iff.mpr (by rw [ih]; exact one_ne_zero)
    rw [← Finset.sum_erase_add _ _ h_leading_in_supp]
    have h_leading_term : (g D_leading • HeckeRing.m (GL_pair 2)
        (HeckeCoset.rep (T_diag (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D_leading)) D_target = 1 := by
      rw [ih]
      simp only [Finsupp.smul_apply, smul_eq_mul, one_mul]
      exact h_leading_mult
    rw [h_leading_term]
    have h_erased : ∀ D₂ ∈ g.support.erase D_leading,
        (g D₂ • HeckeRing.m (GL_pair 2)
          (HeckeCoset.rep (T_diag (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D₂)) D_target = 0 := by
      intro D₂ hD₂
      rw [Finset.mem_erase] at hD₂
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [h_non_leading_mult D₂ hD₂.2 hD₂.1, mul_zero]
    rw [Finset.sum_eq_zero h_erased, zero_add]

/-- **Kronecker delta lemma**: Evaluating the monomial `T_gen(p,0)^a₁ * T_gen(p,1)^b₁` at
the diagonal coset `T(p^b₂, p^(a₂+b₂))` gives 1 iff `(a₁, b₁) = (a₂, b₂)`, and 0 otherwise,
under the hypothesis `b₂ ≤ b₁`.

**Math (Shimura Th 3.24, n=2)**: Using `T_gen(p,1) = T(p,p)` and `T_pp^b₁ = T_elem(p^b₁)`,
the scalar shift reduces the evaluation to `T(1,p)^a₁ (T(1, p^{a₂}))` when `b₁ = b₂`, which
equals `δ_{a₁, a₂}` by the leading coefficient argument. When `b₂ < b₁`, the first entry
`p^b₂` is not divisible by `p^b₁`, so the scalar shift gives 0. -/
lemma monomial_eval_kronecker (p : ℕ) (hp : p.Prime)
    (a₁ b₁ a₂ b₂ : ℕ) (h : b₂ ≤ b₁) :
    (T_gen 2 p 0 ^ a₁ * T_gen 2 p 1 ^ b₁)
        (T_diag (ppowDiag 2 p ![b₂, a₂ + b₂])) =
    if a₁ = a₂ ∧ b₁ = b₂ then 1 else 0 := by
  -- Simplify target: T_diag (ppowDiag 2 p ![b₂, a₂+b₂]) = T_diag ![p^b₂, p^(a₂+b₂)]
  have h_target_eq : (ppowDiag 2 p ![b₂, a₂ + b₂] : Fin 2 → ℕ) =
      (![p ^ b₂, p ^ (a₂ + b₂)] : Fin 2 → ℕ) := by
    funext i; fin_cases i <;> simp [ppowDiag]
  rw [h_target_eq]
  -- Substitute T_gen 2 p 0 = T_ad 1 p and T_gen 2 p 1 = T_pp p
  rw [HeckeRing.GLn.Surj.T_gen_zero_eq_T_ad p hp,
      HeckeRing.GLn.Surj.T_gen_one_eq_T_pp p hp]
  -- Rewrite T_pp p ^ b₁ = T_elem (fun _ => p^b₁)
  rw [HeckeRing.GL2.T_pp_pow p hp b₁]
  -- Case on matching
  by_cases hmatch : a₁ = a₂ ∧ b₁ = b₂
  · rw [if_pos hmatch]
    obtain ⟨ha, hb⟩ := hmatch
    subst ha; subst hb
    -- Target becomes T_diag ![p^b₁, p^(a₁+b₁)]
    -- Write it as T_diag (![1, p^a₁] * (fun _ => p^b₁))
    have h_target_factor : (![p ^ b₁, p ^ (a₁ + b₁)] : Fin 2 → ℕ) =
        (![1, p ^ a₁] : Fin 2 → ℕ) * (fun _ : Fin 2 => p ^ b₁) := by
      funext i; fin_cases i
      · simp [Pi.mul_apply]
      · show p ^ (a₁ + b₁) = p ^ a₁ * p ^ b₁
        rw [pow_add]
    rw [h_target_factor]
    rw [T_mul_T_scalar_eval_shifted (p ^ b₁) (pow_pos hp.pos _) _ _
        (fun i => by fin_cases i <;> simp [pow_pos hp.pos])
        (fun j hj => by
          have hj0 : j = 0 := by omega
          subst hj0
          show (![1, p ^ a₁] : Fin 2 → ℕ) ⟨0, _⟩ ∣ (![1, p ^ a₁] : Fin 2 → ℕ) ⟨0 + 1, _⟩
          exact one_dvd _)]
    exact T_ad_one_p_pow_eval_leading p hp a₁
  · rw [if_neg hmatch]
    -- Non-matching: either b₂ < b₁ (scalar shift gives 0) or b₁ = b₂ with a₁ ≠ a₂ (det mismatch)
    by_cases hbeq : b₁ = b₂
    · -- b₁ = b₂, so a₁ ≠ a₂ (from ¬hmatch)
      have ha_ne : a₁ ≠ a₂ := fun heq => hmatch ⟨heq, hbeq⟩
      subst hbeq
      -- Same as matching case: reduce via scalar shift, but then a₁ ≠ a₂
      have h_target_factor : (![p ^ b₁, p ^ (a₂ + b₁)] : Fin 2 → ℕ) =
          (![1, p ^ a₂] : Fin 2 → ℕ) * (fun _ : Fin 2 => p ^ b₁) := by
        funext i; fin_cases i
        · simp [Pi.mul_apply]
        · show p ^ (a₂ + b₁) = p ^ a₂ * p ^ b₁
          rw [pow_add]
      rw [h_target_factor]
      rw [T_mul_T_scalar_eval_shifted (p ^ b₁) (pow_pos hp.pos _) _ _
          (fun i => by fin_cases i <;> simp [pow_pos hp.pos])
          (fun j hj => by
            have hj0 : j = 0 := by omega
            subst hj0
            show (![1, p ^ a₂] : Fin 2 → ℕ) ⟨0, _⟩ ∣ (![1, p ^ a₂] : Fin 2 → ℕ) ⟨0 + 1, _⟩
            exact one_dvd _)]
      -- (T_ad 1 p)^a₁ (T_diag ![1, p^a₂]) = 0 since a₁ ≠ a₂ (det mismatch)
      -- Use T_gen_pow_support_qpower: if nonzero, det = p^a₁; here det = p^a₂.
      by_contra h_ne_zero
      have hg_eq : (T_ad 1 p) ^ a₁ = (T_gen 2 p 0) ^ a₁ * (T_gen 2 p 1) ^ 0 := by
        simp only [pow_zero, mul_one]
        rw [HeckeRing.GLn.Surj.T_gen_zero_eq_T_ad p hp]
      obtain ⟨a, hDa, ha_pos, ha_div, ha_det⟩ := T_gen_pow_support_qpower ⟨p, hp⟩
          ![a₁, 0] (T_diag (![1, p ^ a₂] : Fin 2 → ℕ)) (hg_eq ▸ h_ne_zero)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_zero,
        add_zero] at ha_det
      have h_a_eq : a = (![1, p ^ a₂] : Fin 2 → ℕ) :=
        diagonal_representative_unique 2 _ _ ha_pos
          (fun i => by fin_cases i <;> simp [pow_pos hp.pos])
          ha_div
          (fun j hj => by
            have hj0 : j = 0 := by omega
            subst hj0
            show (![1, p ^ a₂] : Fin 2 → ℕ) ⟨0, _⟩ ∣ (![1, p ^ a₂] : Fin 2 → ℕ) ⟨0 + 1, _⟩
            exact one_dvd _) hDa.symm
      rw [h_a_eq] at ha_det
      have h_prod : ∏ i, (![1, p ^ a₂] : Fin 2 → ℕ) i = p ^ a₂ := by
        rw [Fin.prod_univ_two]; simp
      rw [h_prod] at ha_det
      have : a₁ = a₂ := Nat.pow_right_injective hp.two_le ha_det.symm
      exact ha_ne this
    · -- b₁ ≠ b₂ (so b₂ < b₁ from hypothesis b₂ ≤ b₁)
      have hb_lt : b₂ < b₁ := lt_of_le_of_ne h (Ne.symm hbeq)
      -- p^b₁ doesn't divide p^b₂ (since b₂ < b₁)
      have h_not_dvd : ¬ p ^ b₁ ∣ (![p ^ b₂, p ^ (a₂ + b₂)] : Fin 2 → ℕ) 0 := by
        simp only [Matrix.cons_val_zero]
        intro h_dvd
        rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h_dvd
        omega
      exact T_mul_T_scalar_eval_zero_of_not_dvd (p ^ b₁) (pow_pos hp.pos _) _ _
        (fun i => by fin_cases i <;> simp [pow_pos hp.pos])
        (fun j hj => by
          have hj0 : j = 0 := by omega
          subst hj0
          show (![p ^ b₂, p ^ (a₂ + b₂)] : Fin 2 → ℕ) ⟨0, _⟩ ∣
               (![p ^ b₂, p ^ (a₂ + b₂)] : Fin 2 → ℕ) ⟨0 + 1, _⟩
          show p ^ b₂ ∣ p ^ (a₂ + b₂)
          exact pow_dvd_pow p (by omega)) 0 h_not_dvd

/-- n=2: evalHom is injective. Uses the Kronecker delta property for `T_gen(0)^a`
    coefficients at first-exponent-zero T_diags, and the scalar shift property
    of `T_gen(1)^b = T(p,p)^b`. -/
theorem evalHom_injective_two (p : ℕ) (hp : p.Prime) :
    Function.Injective (evalHom 2 p) := by
  intro P Q hPQ
  rw [← sub_eq_zero]; set R := P - Q with hR_def
  have hR : evalHom 2 p R = 0 := by simp [R, map_sub, hPQ]
  by_contra hR_ne
  -- R ≠ 0: pick s ∈ R.support minimising the total "second exponent" s 1
  obtain ⟨s, hs_mem, hs_min⟩ := Finset.exists_min_image R.support
    (fun d : Fin 2 →₀ ℕ => d 1)
    (MvPolynomial.support_nonempty.mpr hR_ne)
  have hs_coeff : R.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs_mem
  -- Define the leading coset D_s = T_diag ![p^(s 1), p^(s 0 + s 1)]
  set D_s := T_diag (n := 2) (![p ^ (s 1), p ^ (s 0 + s 1)] : Fin 2 → ℕ)
  -- (evalHom 2 p R)(D_s) = 0
  have h_zero : (evalHom 2 p R) D_s = 0 := by rw [hR]; rfl
  -- Expand evalHom via eval₂_eq'
  change (MvPolynomial.eval₂ (Int.castRingHom (HeckeAlgebra 2))
    (fun k : Fin 2 => T_gen 2 p k) R) D_s = 0 at h_zero
  rw [MvPolynomial.eval₂_eq, Finset.sum_apply'] at h_zero
  -- Rewrite each summand
  have h_term : ∀ d ∈ R.support,
      (((Int.castRingHom (HeckeAlgebra 2)) (R.coeff d)) *
        (∏ k ∈ d.support, T_gen 2 p k ^ d k)) D_s =
      R.coeff d * (∏ k ∈ d.support, T_gen 2 p k ^ d k) D_s := by
    intro d _
    show (((R.coeff d : ℤ) : HeckeAlgebra 2) *
      (∏ k ∈ d.support, T_gen 2 p k ^ d k)) D_s = _
    rw [show ((R.coeff d : ℤ) : HeckeAlgebra 2) =
      (R.coeff d) • (1 : HeckeAlgebra 2) from (zsmul_one _).symm,
      smul_mul_assoc, one_mul, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl h_term] at h_zero
  -- Convert the product over d.support into T_gen(p,0)^(d 0) * T_gen(p,1)^(d 1)
  have h_prod : ∀ d : Fin 2 →₀ ℕ,
      (∏ k ∈ d.support, T_gen 2 p k ^ d k) = T_gen 2 p 0 ^ (d 0) * T_gen 2 p 1 ^ (d 1) := by
    intro d
    -- Use Finset.prod over Fin 2, with d k = 0 giving T_gen^0 = 1 on non-support elements.
    have h_univ : (∏ k ∈ d.support, T_gen 2 p k ^ d k) =
        (∏ k : Fin 2, T_gen 2 p k ^ d k) := by
      apply Finset.prod_subset (Finset.subset_univ _)
      intro k _ hk
      rw [Finsupp.notMem_support_iff.mp hk, pow_zero]
    rw [h_univ, Fin.prod_univ_two]
  conv at h_zero =>
    arg 1; arg 2; ext d
    rw [h_prod d]
  -- Now: ∑ d ∈ R.support, R.coeff d * ((T_gen 0)^(d 0) * (T_gen 1)^(d 1)) D_s = 0
  -- Rewrite D_s using ppowDiag form for monomial_eval_kronecker
  have hD_s_eq : D_s = T_diag (ppowDiag 2 p ![s 1, s 0 + s 1]) := by
    show T_diag (![p ^ (s 1), p ^ (s 0 + s 1)] : Fin 2 → ℕ) =
         T_diag (ppowDiag 2 p ![s 1, s 0 + s 1])
    congr 1
    funext i; fin_cases i <;> simp [ppowDiag]
  rw [hD_s_eq] at h_zero
  -- Apply monomial_eval_kronecker to each term, with (a₁, b₁) = (d 0, d 1), (a₂, b₂) = (s 0, s 1).
  -- Hypothesis b₂ ≤ b₁ (i.e. s 1 ≤ d 1) holds by minimality of s.
  have h_delta : ∀ d ∈ R.support,
      R.coeff d * (T_gen 2 p 0 ^ (d 0) * T_gen 2 p 1 ^ (d 1))
          (T_diag (ppowDiag 2 p ![s 1, s 0 + s 1])) =
      R.coeff d * (if d = s then 1 else 0) := by
    intro d hd_mem
    congr 1
    have h_le : s 1 ≤ d 1 := hs_min d hd_mem
    rw [monomial_eval_kronecker p hp (d 0) (d 1) (s 0) (s 1) h_le]
    -- Convert `if (d 0 = s 0) ∧ (d 1 = s 1) then 1 else 0` to `if d = s then 1 else 0`
    congr 1
    apply propext
    constructor
    · rintro ⟨h0, h1⟩
      ext i; fin_cases i
      · exact h0
      · exact h1
    · intro heq; subst heq; exact ⟨rfl, rfl⟩
  rw [Finset.sum_congr rfl h_delta] at h_zero
  -- Extract the `d = s` term: all others vanish.
  -- Transform `R.coeff d * (if d = s then 1 else 0)` into `if d = s then R.coeff d else 0`.
  have h_rewrite : ∀ d : Fin 2 →₀ ℕ,
      R.coeff d * (if d = s then (1 : ℤ) else 0) =
      if d = s then R.coeff d else 0 := by
    intro d; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun d _ => h_rewrite d)] at h_zero
  -- Now: ∑ d ∈ R.support, (if d = s then R.coeff d else 0) = 0
  rw [Finset.sum_ite_eq_of_mem' R.support s _ hs_mem] at h_zero
  -- h_zero : R.coeff s = 0 (in ℤ)
  exact hs_coeff h_zero

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

/-- Shimura Theorem 3.20 at `n = 2`: `R_p^{(2)} ≅ ℤ[X₁, X₂]`. This is the clean,
    axiom-free specialisation: it calls `Surj.T_gen_generates_R_p_two` and
    `Inj.evalHom_injective_two` directly, bypassing the bundled all-`n`
    `T_gen_generates_R_p` / `evalHom_injective` (whose general-`n` case is still a
    `sorry`). Use this in the GL2 path instead of `R_p_isPolynomialRing 2 …`. -/
noncomputable def R_p_isPolynomialRing_two (p : ℕ) (hp : p.Prime) :
    MvPolynomial (Fin 2) ℤ ≃+* R_p 2 p hp :=
  RingEquiv.ofBijective (Inj.evalHomR 2 p hp)
    ⟨Inj.evalHomR_injective 2 p hp (Inj.evalHom_injective_two p hp),
     Inj.evalHomR_surjective 2 p hp (Surj.T_gen_generates_R_p_two p hp)⟩

end HeckeRing.GLn
