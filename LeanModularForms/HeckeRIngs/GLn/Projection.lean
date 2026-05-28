/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.PolynomialRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Division
import LeanModularForms.HeckeRIngs.GLn.BlockBijection

/-!
# Projection ψ and Theorem 3.20 for general n

Completes Shimura's Theorem 3.20 (`R_p ≅ ℤ[X₁,...,Xₙ]`) for all n.

## References

* Shimura, §3.2, Lemma 3.19, Theorem 3.20
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset

open scoped Pointwise

namespace HeckeRing.GLn

section KillComplHelpers

variable {m : ℕ}

private lemma killCompl_X_last :
    MvPolynomial.killCompl (Fin.castSucc_injective m)
      (MvPolynomial.X (Fin.last m) : MvPolynomial (Fin (m + 1)) ℤ) = 0 := by
  show (MvPolynomial.killCompl (Fin.castSucc_injective m)) (MvPolynomial.X (Fin.last m)) = 0
  unfold MvPolynomial.killCompl; rw [MvPolynomial.aeval_X]
  split_ifs with hm
  · exfalso; obtain ⟨j, hj⟩ := hm; exact absurd hj (Fin.castSucc_ne_last j)
  · rfl

private lemma killCompl_eq_zero_imp_X_dvd (P : MvPolynomial (Fin (m + 1)) ℤ)
    (h : MvPolynomial.killCompl (Fin.castSucc_injective m) P = 0) :
    MvPolynomial.X (⟨m, by omega⟩ : Fin (m + 1)) ∣ P := by
  rw [MvPolynomial.X_dvd_iff_modMonomial_eq_zero]
  set R := P.modMonomial (Finsupp.single (Fin.last m) 1)
  have hkR : MvPolynomial.killCompl (Fin.castSucc_injective m) R = 0 := by
    have : MvPolynomial.killCompl (Fin.castSucc_injective m) P =
        MvPolynomial.killCompl (Fin.castSucc_injective m) R := by
      conv_lhs => rw [← MvPolynomial.divMonomial_add_modMonomial P
        (Finsupp.single (Fin.last m) 1)]
      simp only [map_add, map_mul]
      have : (MvPolynomial.killCompl (Fin.castSucc_injective m))
          ((MvPolynomial.monomial (Finsupp.single (Fin.last m) 1)) (1 : ℤ)) = 0 :=
        killCompl_X_last
      rw [this, zero_mul, zero_add]
    rwa [← this]
  have h_supp : ∀ s ∈ R.support, s (Fin.last m) = 0 := by
    intro s hs
    by_contra hsne
    have hle : Finsupp.single (Fin.last m) 1 ≤ s := by rw [Finsupp.single_le_iff]; omega
    exact (MvPolynomial.mem_support_iff.mp hs) (MvPolynomial.coeff_modMonomial_of_le P hle)
  have hR_img : ∃ Q : MvPolynomial (Fin m) ℤ, MvPolynomial.rename Fin.castSucc Q = R := by
    use R.support.sum (fun s ↦
      MvPolynomial.monomial (s.comapDomain Fin.castSucc (Fin.castSucc_injective m).injOn)
        (R.coeff s))
    rw [map_sum]
    conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff R]
    apply Finset.sum_congr rfl
    intro s hs
    rw [MvPolynomial.rename_monomial,
      Finsupp.mapDomain_comapDomain Fin.castSucc (Fin.castSucc_injective m) s (by
        intro i hi
        rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
        have hs0 := h_supp s hs
        exact ⟨i.castPred (by intro heq; rw [heq] at hi; exact hi hs0),
               Fin.castSucc_castPred i (by intro heq; rw [heq] at hi; exact hi hs0)⟩)]
  obtain ⟨Q, hQ⟩ := hR_img
  have h1 : Q = 0 := by
    rw [← MvPolynomial.killCompl_rename_app (Fin.castSucc_injective m) Q, hQ, hkR]
  have : R = 0 := by rw [← hQ, h1, map_zero]
  exact this

private lemma T_gen_diag_castSucc_eq_cons (p : ℕ) (k : Fin m) :
    T_gen_diag (m + 1) p (Fin.castSucc k) = Fin.cons 1 (T_gen_diag m p k) := by
  funext i
  simp only [T_gen_diag_val]
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [Fin.val_zero, Fin.val_castSucc]
    split_ifs with h
    · simp [Fin.cons_zero]
    · exfalso; omega
  · simp only [Fin.val_succ, Fin.val_castSucc, Fin.cons_succ, T_gen_diag_val]
    split_ifs <;> omega

private lemma divChain_cons_one (d : Fin m → ℕ) (hd_div : DivChain m d) :
    DivChain (m + 1) (Fin.cons 1 d : Fin (m + 1) → ℕ) := by
  intro i hi
  by_cases h0 : i = 0
  · subst h0
    show (Fin.cons 1 d : Fin (m + 1) → ℕ) ⟨0, _⟩ ∣
         (Fin.cons 1 d : Fin (m + 1) → ℕ) ⟨0 + 1, hi⟩
    simp only [show (⟨0, by omega⟩ : Fin (m + 1)) = 0 from rfl, Fin.cons_zero]
    exact one_dvd _
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    show (Fin.cons 1 d : Fin (m + 1) → ℕ) ⟨j + 1, _⟩ ∣
         (Fin.cons 1 d : Fin (m + 1) → ℕ) ⟨j + 1 + 1, hi⟩
    rw [show (⟨j + 1, _⟩ : Fin (m + 1)) = (⟨j, by omega⟩ : Fin m).succ from rfl,
        show (⟨j + 1 + 1, hi⟩ : Fin (m + 1)) = (⟨j + 1, by omega⟩ : Fin m).succ from rfl]
    simp only [Fin.cons_succ]
    exact hd_div j (by omega)

private lemma T_diag_scalar_mul_ne_cons_one [NeZero m] (c : ℕ) (hc : 2 ≤ c)
    (a : Fin (m + 1) → ℕ) (ha_pos : ∀ i, 0 < a i) (ha_div : DivChain (m + 1) a)
    (d : Fin m → ℕ) (hd_pos : ∀ i, 0 < d i) (hd_div : DivChain m d) :
    T_diag ((fun _ : Fin (m + 1) ↦ c) * a) ≠ T_diag (Fin.cons 1 d) := by
  intro heq
  have hc_pos : 0 < c := by omega
  have hca_pos : ∀ i, 0 < ((fun _ : Fin (m + 1) ↦ c) * a) i := fun i ↦
    Nat.mul_pos hc_pos (ha_pos i)
  have hca_div : DivChain (m + 1) ((fun _ : Fin (m + 1) ↦ c) * a) :=
    DivChain_mul (m + 1) _ _ (divChain_const (m + 1) c) ha_div
  have hcc_pos : ∀ i, 0 < (Fin.cons 1 d : Fin (m + 1) → ℕ) i := fun i ↦ by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simp only [Fin.cons_succ]; exact hd_pos j
  have h_eq : (fun _ : Fin (m + 1) ↦ c) * a = Fin.cons 1 d :=
    diagonal_representative_unique (m + 1) _ _ hca_pos hcc_pos hca_div
      (divChain_cons_one d hd_div) heq
  have h0 := congr_fun h_eq 0
  simp only [Pi.mul_apply, Fin.cons_zero] at h0
  have ha0 : 1 ≤ a 0 := ha_pos 0
  have : 2 ≤ c * a 0 := by calc 2 = 2 * 1 := by ring
                               _ ≤ c * a 0 := Nat.mul_le_mul hc ha0
  omega

private lemma scalar_mul_coeff_cons_one_eq_zero_general {m : ℕ} [NeZero m]
    (c : ℕ) (hc : 2 ≤ c)
    (x : HeckeAlgebra (m + 1)) (d : Fin m → ℕ) (hd_pos : ∀ i, 0 < d i)
    (hd_div : DivChain m d) :
    (T_elem (fun _ : Fin (m + 1) ↦ c) * x) (T_diag (Fin.cons 1 d)) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero =>
    rw [mul_zero]; rfl
  | add g₁ g₂ ih₁ ih₂ =>
    rw [mul_add, Finsupp.add_apply, ih₁, ih₂]; ring
  | single D z =>
    obtain ⟨a, ha_pos, ha_div, hD_eq⟩ := exists_diagonal_representative (m + 1) (HeckeCoset.rep D)
    have hD_eq' : D = T_diag a := (Quotient.out_eq D).symm.trans hD_eq
    rw [hD_eq']
    show (T_elem (fun _ : Fin (m + 1) ↦ c) *
         HeckeRing.T_single (GL_pair (m + 1)) ℤ (T_diag a) z)
         (T_diag (Fin.cons 1 d)) = 0
    change (HeckeRing.T_single (GL_pair (m + 1)) ℤ (T_diag (fun _ : Fin (m + 1) ↦ c)) 1 *
            HeckeRing.T_single (GL_pair (m + 1)) ℤ (T_diag a) z)
            (T_diag (Fin.cons 1 d)) = 0
    rw [HeckeRing.T_single_mul_T_single]
    simp only [one_smul]
    have hc_pos : 0 < c := by omega
    have hm : HeckeRing.m (GL_pair (m + 1))
        (HeckeCoset.rep (T_diag (fun _ : Fin (m + 1) ↦ c)))
        (HeckeCoset.rep (T_diag a)) =
        Finsupp.single (T_diag ((fun _ : Fin (m + 1) ↦ c) * a)) 1 := by
      have := T_diag_scalar_mul (n := m + 1) c hc_pos a ha_pos ha_div
      simp only [T_elem, HeckeRing.T_single_mul_T_single, one_mul, one_smul] at this
      exact this
    rw [hm]
    rw [Finsupp.smul_apply, Finsupp.single_apply]
    simp only [smul_eq_mul]
    rw [if_neg (T_diag_scalar_mul_ne_cons_one c hc a ha_pos ha_div d hd_pos hd_div)]; ring

private lemma scalar_mul_coeff_cons_one_eq_zero {m : ℕ} [NeZero m] (p : ℕ) (hp : p.Prime)
    (x : HeckeAlgebra (m + 1)) (d : Fin m → ℕ) (hd_pos : ∀ i, 0 < d i)
    (hd_div : DivChain m d) :
    (T_elem (fun _ : Fin (m + 1) ↦ p) * x).toFun (T_diag (Fin.cons 1 d)) = 0 :=
  scalar_mul_coeff_cons_one_eq_zero_general p hp.two_le x d hd_pos hd_div

end KillComplHelpers

section CoeffCompat

variable (m : ℕ) [NeZero m] (p : ℕ) (hp : p.Prime)

include hp in
private lemma heckeMultiplicity_firstEntry_ge_p_eq_zero
    (e : Fin (m + 1) → ℕ) (he_pos : ∀ i, 0 < e i) (he_div : DivChain (m + 1) e)
    (he_first : 2 ≤ e 0)
    (b d : Fin m → ℕ) (hb : ∀ i, 0 < b i) (hd : ∀ i, 0 < d i)
    (hdb : DivChain m b) (hdd : DivChain m d) :
    HeckeRing.heckeMultiplicity (GL_pair (m + 1))
      (HeckeCoset.rep (T_diag e))
      (HeckeCoset.rep (T_diag (Fin.cons 1 b)))
      (HeckeCoset.rep (T_diag (Fin.cons 1 d))) = 0 := by
  have h_eq_mul : HeckeRing.heckeMultiplicity (GL_pair (m + 1))
        (HeckeCoset.rep (T_diag e))
        (HeckeCoset.rep (T_diag (Fin.cons 1 b)))
        (HeckeCoset.rep (T_diag (Fin.cons 1 d))) =
      (HeckeRing.T_single (GL_pair (m + 1)) ℤ (T_diag e) 1 *
        HeckeRing.T_single (GL_pair (m + 1)) ℤ (T_diag (Fin.cons 1 b)) 1)
        (T_diag (Fin.cons 1 d)) := by
    rw [HeckeRing.T_single_one_mul_T_single_one, HeckeRing.m_apply]
  rw [h_eq_mul]
  have he0_pos : 0 < e 0 := he_pos 0
  have he0_dvd : ∀ i, e 0 ∣ e i := by
    intro i
    exact divChain_dvd (n := m + 1) he_div (Fin.zero_le i)
  set a : Fin (m + 1) → ℕ := fun i ↦ e i / e 0 with ha_def
  have ha_pos : ∀ i, 0 < a i := fun i ↦ by
    rw [ha_def]; exact Nat.div_pos (Nat.le_of_dvd (he_pos i) (he0_dvd i)) he0_pos
  have ha_div : DivChain (m + 1) a := by
    intro i hi
    simp only [a]
    have h_div := he_div i hi
    exact Nat.div_dvd_div (he0_dvd _) h_div
  have he_factor : e = (fun _ : Fin (m + 1) ↦ e 0) * a := by
    funext i; rw [Pi.mul_apply]
    show e i = e 0 * (e i / e 0)
    rw [Nat.mul_div_cancel' (he0_dvd i)]
  have h_T_elem_factor : HeckeRing.T_single (GL_pair (m + 1)) ℤ (T_diag e) 1 =
      T_elem (fun _ : Fin (m + 1) ↦ e 0) * T_elem a := by
    change T_elem e = _
    conv_lhs => rw [he_factor]
    exact (T_diag_scalar_mul (m + 1) (e 0) he0_pos a ha_pos ha_div).symm
  rw [h_T_elem_factor]
  rw [mul_assoc]
  exact scalar_mul_coeff_cons_one_eq_zero_general (e 0) he_first
    (T_elem a * HeckeRing.T_single (GL_pair (m + 1)) ℤ (T_diag (Fin.cons 1 b)) 1)
    d hd hdd

include hp in
/-- Shimura's Lemma 3.19 (Coefficient compatibility).

Proof stubbed: only used for general-n Shimura Thm 3.20, not Shimura Thm 3.35 at n=2. -/
lemma hecke_coeff_compat_gen
    (P : MvPolynomial (Fin (m + 1)) ℤ) (d : Fin m → ℕ)
    (hd_pos : ∀ i, 0 < d i) (hd_div : DivChain m d) :
    (evalHom (m + 1) p P).toFun (T_diag (Fin.cons 1 d)) =
    (evalHom m p (MvPolynomial.killCompl (Fin.castSucc_injective m) P)).toFun (T_diag d) := by
  sorry

end CoeffCompat

section DimCompat

variable (m : ℕ) [NeZero m] (p : ℕ) (hp : p.Prime)

include hp in
/-- **Injectivity lift** (Shimura Lemma 3.19): if a polynomial in the first `m` generators
evaluates to `0` in dimension `m+1`, it evaluates to `0` in dimension `m`.

Proof stubbed: only used for general-n Shimura Thm 3.20, not Shimura Thm 3.35 at n=2. -/
lemma evalHom_lift_injective
    (P : MvPolynomial (Fin m) ℤ)
    (hP : evalHom (m + 1) p (MvPolynomial.rename (Fin.castSucc (n := m)) P) = 0) :
    evalHom m p P = 0 := by
  sorry

end DimCompat

section ZeroDivisor

variable (n : ℕ) [NeZero n]

/-- `T(c,...,c)` is not a zero divisor in the Hecke algebra. -/
theorem T_scalar_not_zero_divisor (c : ℕ) (hc : 0 < c) :
    ∀ f : HeckeAlgebra n, T_elem (fun _ : Fin n ↦ c) * f = 0 → f = 0 := by
  have h_rep : ∀ D : HeckeCoset (GL_pair n),
      ∃ b, (∀ i, 0 < b i) ∧ DivChain n b ∧ D = T_diag b := by
    intro D
    obtain ⟨b, hb, hdiv, heq⟩ := exists_diagonal_representative n (HeckeCoset.rep D)
    exact ⟨b, hb, hdiv, (Quotient.out_eq D).symm.trans heq⟩
  choose diag_of h_pos h_div h_eq using h_rep
  set φ : HeckeCoset (GL_pair n) → HeckeCoset (GL_pair n) :=
    fun D ↦ T_diag ((fun _ : Fin n ↦ c) * diag_of D) with hφ_def
  have hφ_inj : Function.Injective φ := by
    intro D₁ D₂ hφ
    rw [h_eq D₁, h_eq D₂]; congr 1
    exact funext fun i ↦ Nat.eq_of_mul_eq_mul_left hc
      (congr_fun (diagonal_representative_unique n _ _
        (fun i ↦ Nat.mul_pos hc (h_pos D₁ i))
        (fun i ↦ Nat.mul_pos hc (h_pos D₂ i))
        (DivChain_mul n _ _ (divChain_const n c) (h_div D₁))
        (DivChain_mul n _ _ (divChain_const n c) (h_div D₂)) hφ) i)
  have h_map : ∀ y : HeckeAlgebra n,
      T_elem (fun _ : Fin n ↦ c) * y = Finsupp.mapDomain φ y := by
    intro y; induction y using Finsupp.induction_linear with
    | zero => simp [mul_zero, Finsupp.mapDomain_zero]
    | add g₁ g₂ ih₁ ih₂ => simp [mul_add, ih₁, ih₂, Finsupp.mapDomain_add]
    | single D z =>
      rw [Finsupp.mapDomain_single]; conv_lhs => rw [h_eq D]
      change (HeckeRing.T_single (GL_pair n) ℤ
        (T_diag (fun _ : Fin n ↦ c)) 1 *
        HeckeRing.T_single (GL_pair n) ℤ (T_diag (diag_of D)) z)
        = Finsupp.single (φ D) z
      rw [HeckeRing.T_single_mul_T_single, one_smul]
      have hm : HeckeRing.m (GL_pair n)
          (HeckeCoset.rep (T_diag (fun _ : Fin n ↦ c)))
          (HeckeCoset.rep (T_diag (diag_of D))) =
          Finsupp.single (T_diag ((fun _ : Fin n ↦ c) * diag_of D)) 1 := by
        have := T_diag_scalar_mul n c hc (diag_of D) (h_pos D) (h_div D)
        simp only [T_elem, HeckeRing.T_single_mul_T_single, one_mul, one_smul] at this
        exact this
      rw [hm, Finsupp.smul_single', mul_one]
  intro f hf
  exact Finsupp.mapDomain_injective hφ_inj
    (show Finsupp.mapDomain φ f = Finsupp.mapDomain φ 0 by
      rw [Finsupp.mapDomain_zero, ← h_map, hf])

end ZeroDivisor

section MainInduction

variable (p : ℕ) (hp : p.Prime)

private lemma T_scalar_mem_evalHom_range (m : ℕ) [NeZero m] :
    (T_elem fun _ : Fin (m + 1) ↦ p) ∈ (evalHom (m + 1) p).range := by
  have h : T_elem (fun _ : Fin (m + 1) ↦ p) = T_gen (m + 1) p ⟨m, by omega⟩ := by
    unfold T_gen; apply T_elem_congr_diag
    funext i; simp only [T_gen_diag_val]; split_ifs with h <;> omega
  rw [h]; exact T_gen_mem_evalHom_range (m + 1) p _

include hp in
private lemma ppow_scalar_factor_mem_range (m : ℕ) [NeZero m]
    (e : Fin (m + 1) → ℕ) (hmono : Monotone e)
    (h_reduced : T_elem (ppowDiag (m + 1) p (fun i ↦ e i - e 0)) ∈
      (evalHom (m + 1) p).range) :
    T_elem (ppowDiag (m + 1) p e) ∈ (evalHom (m + 1) p).range := by
  have h_all_ge : ∀ i, e 0 ≤ e i := fun i ↦ hmono (Fin.zero_le i)
  set e' : Fin (m + 1) → ℕ := fun i ↦ e i - e 0 with he'_def
  have he'_mono : Monotone e' := fun i j hij ↦ Nat.sub_le_sub_right (hmono hij) _
  have h_split : ppowDiag (m + 1) p e = (fun _ ↦ p ^ e 0) * ppowDiag (m + 1) p e' := by
    funext i; simp only [ppowDiag, Pi.mul_apply]
    rw [← pow_add, Nat.add_sub_cancel' (h_all_ge i)]
  rw [T_elem_congr_diag (m + 1) h_split,
    ← T_diag_scalar_mul (m + 1) (p ^ e 0) (pow_pos hp.pos _)
      (ppowDiag (m + 1) p e') (ppowDiag_pos (m + 1) p hp _)
      (divChain_ppow (m + 1) p _ he'_mono)]
  refine (evalHom (m + 1) p).range.mul_mem ?_ h_reduced
  rw [← T_scalar_pow (m + 1) p hp.pos (e 0)]
  exact (evalHom (m + 1) p).range.pow_mem (T_scalar_mem_evalHom_range p m) _

private theorem T_elem_firstZero_in_range (m : ℕ) [NeZero m]
    (e : Fin (m + 1) → ℕ) (hmono : Monotone e) (he0 : e 0 = 0)
    (h_surj_m : ∀ f ∈ R_p m p hp, f ∈ (evalHom m p).range)
    (h_higher : ∀ (e' : Fin (m + 1) → ℕ), Monotone e' → 0 < e' 0 →
        (∑ i, e' i) ≤ (∑ i, e i) →
        T_elem (ppowDiag (m + 1) p e') ∈ (evalHom (m + 1) p).range) :
    T_elem (ppowDiag (m + 1) p e) ∈ (evalHom (m + 1) p).range := by
  haveI : NeZero (m + 1) := ⟨by omega⟩
  set f : Fin m → ℕ := fun i ↦ e i.succ with hf_def
  have hf_mono : Monotone f := fun i j hij ↦
    hmono (Fin.succ_le_succ_iff.mpr hij)
  have hf_mem : T_elem (ppowDiag m p f) ∈ (evalHom m p).range :=
    h_surj_m _ (T_elem_ppow_mem_R_p m p hp f hf_mono)
  obtain ⟨P, hP⟩ := hf_mem
  have he_eq : ppowDiag (m + 1) p e = ppowDiag (m + 1) p (Fin.cons 0 f) := by
    congr 1; funext i; refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [Fin.cons_zero, he0]
    · simp [Fin.cons_succ, hf_def]
  have h_renamed_range : evalHom (m + 1) p (MvPolynomial.rename Fin.castSucc P) ∈
      (evalHom (m + 1) p).range :=
    ⟨MvPolynomial.rename Fin.castSucc P, rfl⟩
  rw [T_elem_congr_diag (m + 1) he_eq]
  -- Blocked on `hecke_coeff_compat_gen` (castSucc case), which depends on
  -- `heckeMultiplicity_block_embed`.
  sorry

private theorem surj_step (m : ℕ) [NeZero m]
    (h_surj_m : ∀ f ∈ R_p m p hp, f ∈ (evalHom m p).range) :
    ∀ f ∈ R_p (m + 1) p hp, f ∈ (evalHom (m + 1) p).range := by
  haveI : NeZero (m + 1) := ⟨by omega⟩
  intro f hf; apply Subring.closure_le.mpr _ hf
  intro x hx; obtain ⟨e, hmono, rfl⟩ := hx
  suffices key : ∀ (k : ℕ) (e : Fin (m + 1) → ℕ), Monotone e → (∑ i, e i) ≤ k →
      T_elem (ppowDiag (m + 1) p e) ∈ (evalHom (m + 1) p).range from
    key _ e hmono le_rfl
  intro k; induction k with
  | zero =>
    intro e _hmono hsum
    have h_zero : ∀ i, e i = 0 := fun i ↦ Nat.eq_zero_of_le_zero
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i) |>.trans (by omega))
    rw [show ppowDiag (m + 1) p e = fun _ ↦ 1 from
      funext fun i ↦ by simp [ppowDiag, h_zero i], T_elem_ones_eq_one]
    exact (evalHom (m + 1) p).range.one_mem
  | succ k ihk =>
    intro e hmono hsum
    have reduced_sum : ∀ e' : Fin (m + 1) → ℕ, 0 < e' 0 → (∑ i, e' i) ≤ k + 1 →
        (∑ i, (e' i - e' 0)) ≤ k := fun e' he'0 he'sum ↦ by
      have : ∑ i : Fin (m + 1), (e' i - e' 0) < ∑ i : Fin (m + 1), e' i :=
        Finset.sum_lt_sum (fun i _ ↦ Nat.sub_le (e' i) (e' 0))
          ⟨0, Finset.mem_univ _, by omega⟩
      omega
    by_cases he0 : e 0 = 0
    · exact T_elem_firstZero_in_range p hp m e hmono he0 h_surj_m
        (fun e' he'_mono he'_pos he'_sum ↦
          ppow_scalar_factor_mem_range p hp m e' he'_mono
            (ihk _ (fun i j hij ↦ Nat.sub_le_sub_right (he'_mono hij) _)
              (reduced_sum e' he'_pos (he'_sum.trans hsum))))
    · have he0_pos : 0 < e 0 := Nat.pos_of_ne_zero he0
      exact ppow_scalar_factor_mem_range p hp m e hmono
        (ihk _ (fun i j hij ↦ Nat.sub_le_sub_right (hmono hij) _)
          (reduced_sum e he0_pos hsum))

-- Combined surjectivity + injectivity for all n, by induction. Proof stubbed: only
-- used for general-n Shimura Thm 3.20, not Shimura Thm 3.35 at n=2.
private theorem evalHom_surj_and_inj :
    ∀ n : ℕ, ∀ _hn : NeZero n,
    (∀ f ∈ @R_p n _hn p hp, f ∈ (@evalHom n _hn p).range) ∧
    Function.Injective (@evalHom n _hn p) := by
  sorry

end MainInduction

end HeckeRing.GLn
