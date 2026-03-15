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

* `mk2` — construct a `Fin 2 → ℕ+` diagonal
* `T_ad` — `T(a,d)` basis element
* `T_pp` — scalar double coset `T(p,p)`
* `T_sum` — Shimura's `T(m) = Σ T(a,d)` over divisor pairs

## References

* Shimura, §3.2, Theorem 3.24
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset HeckeRing.GLn

open scoped Pointwise

namespace HeckeRing.GL2

/-! ### Two-dimensional diagonals -/

/-- Construct a `Fin 2 → ℕ+` diagonal from two values. -/
def mk2 (a d : ℕ+) : Fin 2 → ℕ+ :=
  ![a, d]

@[simp] lemma mk2_zero (a d : ℕ+) : mk2 a d 0 = a := rfl

@[simp] lemma mk2_one (a d : ℕ+) : mk2 a d 1 = d := rfl

/-- DivChain for n=2 reduces to `a ∣ d`. -/
lemma divChain_mk2 (a d : ℕ+) (h : (a : ℕ) ∣ (d : ℕ)) :
    DivChain 2 (mk2 a d) := by
  intro i hi
  have : i = 0 := by omega
  subst this
  simpa [mk2] using h

/-- A constant `Fin 2 → ℕ+` function equals `mk2 c c`. -/
lemma const_eq_mk2 (c : ℕ+) : (fun (_ : Fin 2) => c) = mk2 c c :=
  funext fun i => by fin_cases i <;> rfl

/-! ### Basis elements -/

/-- `T(a,d)` for n=2: the Hecke basis element for diagonal `(a,d)` with `a ∣ d`. -/
noncomputable def T_ad (a d : ℕ+) (h : (a : ℕ) ∣ (d : ℕ)) :
    HeckeAlgebra 2 :=
  T_elem 2 (mk2 a d) (divChain_mk2 a d h)

/-- `T(p,p)` — the scalar double coset. -/
noncomputable def T_pp (p : ℕ) (hp : p.Prime) : HeckeAlgebra 2 :=
  T_elem 2 (fun _ => ⟨p, hp.pos⟩) (divChain_const 2 ⟨p, hp.pos⟩)

/-- T(p,p) equals T_ad(p,p). -/
lemma T_pp_eq_T_ad (p : ℕ) (hp : p.Prime) :
    T_pp p hp = T_ad ⟨p, hp.pos⟩ ⟨p, hp.pos⟩ (dvd_refl _) := by
  unfold T_pp T_ad
  exact T_elem_congr_diag 2 (const_eq_mk2 ⟨p, hp.pos⟩) _ _

/-- `T(1,...,1)` is the multiplicative identity. -/
lemma T_elem_ones_eq : T_elem 2 (fun _ => (1 : ℕ+)) (divChain_const 2 1) = 1 := by
  show T_single (GL_pair 2) ℤ (T_diag 2 (fun _ => 1) (divChain_const 2 1)) 1 = 1
  rw [T_diag_ones 2]
  exact (one_eq_T_single (GL_pair 2)).symm

/-- T(1,1) is the identity element. -/
lemma T_ad_one_one : T_ad 1 1 (dvd_refl _) = 1 := by
  unfold T_ad
  have h := T_elem_congr_diag 2 (const_eq_mk2 1).symm (divChain_mk2 1 1 (dvd_refl _))
    (divChain_const 2 1)
  rw [h]
  exact T_elem_ones_eq

/-! ### T(m): sum over divisor pairs -/

/-- Helper: `T(a,d)` from natural numbers, returning 0 if conditions fail. -/
noncomputable def T_ad' (a d : ℕ) : HeckeAlgebra 2 :=
  if h : 0 < a ∧ 0 < d ∧ a ∣ d then
    T_ad ⟨a, h.1⟩ ⟨d, h.2.1⟩ h.2.2
  else 0

/-- `T(m) = Σ_{a ∣ m} T_ad'(a, m/a)`.
    Only terms with `a² ∣ m` contribute (others vanish via `T_ad'`). -/
noncomputable def T_sum (m : ℕ+) : HeckeAlgebra 2 :=
  ∑ a ∈ (m : ℕ).divisors, T_ad' a ((m : ℕ) / a)

/-! ### Structural lemmas -/

section Structural

variable (p : ℕ) (hp : p.Prime)

/-- Helper: double coset equality from membership. -/
private lemma doubleCoset_eq_of_mem' (g δ : GL (Fin 2) ℚ)
    (h : g ∈ DoubleCoset.doubleCoset δ (SLnZ_subgroup 2) (SLnZ_subgroup 2)) :
    DoubleCoset.doubleCoset g (SLnZ_subgroup 2) (SLnZ_subgroup 2) =
    DoubleCoset.doubleCoset δ (SLnZ_subgroup 2) (SLnZ_subgroup 2) := by
  rw [DoubleCoset.mem_doubleCoset] at h
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := h
  rw [heq]
  exact (DoubleCoset.doubleCoset_mul_right_eq_self (GL_pair 2) ⟨h₂, hh₂⟩ (h₁ * δ)).trans
    (doset_mul_left_eq_self (GL_pair 2) ⟨h₁, hh₁⟩ δ)

/-- For p prime, T(p) = T_ad(1,p). The only divisor pair is (1,p). -/
lemma T_sum_prime :
    T_sum ⟨p, hp.pos⟩ = T_ad 1 ⟨p, hp.pos⟩ (one_dvd _) := by
  show ∑ a ∈ p.divisors, T_ad' a (p / a) = _
  rw [hp.sum_divisors, Nat.div_self hp.pos, Nat.div_one]
  -- T_ad' p 1 = 0 since ¬(p ∣ 1) for prime p
  have h1 : T_ad' p 1 = 0 := by
    unfold T_ad'
    rw [dif_neg]
    push_neg
    intro _ _
    exact fun hdvd => hp.one_lt.not_ge (Nat.le_of_dvd Nat.one_pos hdvd)
  -- T_ad' 1 p = T_ad 1 ⟨p, hp.pos⟩ (one_dvd _)
  have h2 : T_ad' 1 p = T_ad 1 ⟨p, hp.pos⟩ (one_dvd _) := by
    unfold T_ad'
    rw [dif_pos ⟨Nat.one_pos, hp.pos, one_dvd p⟩]
    rfl
  rw [h1, h2, zero_add]

/-- Pointwise multiplication of PNat sequences commutes with a constant. -/
private lemma pnatMul_scalar_comm (b : Fin 2 → ℕ+) (c : ℕ+) :
    pnatMul 2 b (fun _ => c) = pnatMul 2 (fun _ => c) b := by
  ext i; exact Subtype.ext (Nat.mul_comm _ _)

/-- For right-scalar multiplication, `mulMap` sends every pair to `T_diag(bc)`. -/
private lemma mulMap_right_scalar_eq (b : Fin 2 → ℕ+) (hb : DivChain 2 b) (c : ℕ+)
    (hbc : DivChain 2 (pnatMul 2 b (fun _ => c)))
    (p : decompQuot (GL_pair 2) (T_diag 2 b hb) ×
         decompQuot (GL_pair 2) (T_diag 2 (fun _ => c) (divChain_const 2 c))) :
    mulMap (GL_pair 2) (T_diag 2 b hb)
      (T_diag 2 (fun _ => c) (divChain_const 2 c)) p =
    T_diag 2 (pnatMul 2 b (fun _ => c)) hbc := by
  set H := (GL_pair 2).H
  -- Step 1: δ_b ∈ DC(diagMat(b))
  have hδb_mem : ((T_diag 2 b hb).eql.choose : GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (diagMat 2 b : GL (Fin 2) ℚ) H H := by
    have h_spec := (T_diag 2 b hb).eql.choose_spec
    simp only [T_diag, T_mk, diagMat_delta] at h_spec
    rw [h_spec]; exact DoubleCoset.mem_doubleCoset_self H H _
  rw [DoubleCoset.mem_doubleCoset] at hδb_mem
  obtain ⟨h₁b, hh₁b, h₂b, hh₂b, hδb_eq⟩ := hδb_mem
  -- Step 2: δ_c ∈ DC(diagMat(c,...,c))
  have hδc_mem : ((T_diag 2 (fun _ => c) (divChain_const 2 c)).eql.choose : GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (diagMat 2 (fun _ => c) : GL (Fin 2) ℚ) H H := by
    have h_spec := (T_diag 2 (fun _ => c) (divChain_const 2 c)).eql.choose_spec
    simp only [T_diag, T_mk, diagMat_delta] at h_spec
    rw [h_spec]; exact DoubleCoset.mem_doubleCoset_self H H _
  rw [DoubleCoset.mem_doubleCoset] at hδc_mem
  obtain ⟨h₁c, hh₁c, h₂c, hh₂c, hδc_eq⟩ := hδc_mem
  -- Step 3: Product ∈ DC(diagMat(bc)) using scalar commutativity
  have h_product_mem : (p.1.out : GL (Fin 2) ℚ) *
      ((T_diag 2 b hb).eql.choose : GL (Fin 2) ℚ) *
      ((p.2.out : GL (Fin 2) ℚ) * ((T_diag 2 (fun _ => c) (divChain_const 2 c)).eql.choose : GL (Fin 2) ℚ)) ∈
      DoubleCoset.doubleCoset (diagMat 2 (pnatMul 2 b (fun _ => c)) : GL (Fin 2) ℚ) H H := by
    rw [DoubleCoset.mem_doubleCoset]
    set x1 := (↑(Quotient.out p.1) : GL (Fin 2) ℚ)
    set db := ((T_diag 2 b hb).eql.choose : GL (Fin 2) ℚ)
    set x2 := (↑(Quotient.out p.2) : GL (Fin 2) ℚ)
    set dc := ((T_diag 2 (fun _ => c) (divChain_const 2 c)).eql.choose : GL (Fin 2) ℚ)
    refine ⟨(p.1.out : GL (Fin 2) ℚ) * h₁b,
            H.mul_mem (SetLike.coe_mem p.1.out) hh₁b,
            h₂b * p.2.out * h₁c * h₂c,
            H.mul_mem (H.mul_mem (H.mul_mem hh₂b (SetLike.coe_mem p.2.out)) hh₁c) hh₂c,
            ?_⟩
    rw [show db = h₁b * diagMat 2 b * h₂b from hδb_eq,
        show dc = h₁c * diagMat 2 (fun _ => c) * h₂c from hδc_eq]
    have h_comm : diagMat 2 (fun _ => c) * (h₂b * x2 * h₁c) =
        (h₂b * x2 * h₁c) * diagMat 2 (fun _ => c) :=
      diagMat_scalar_comm 2 c (h₂b * x2 * h₁c)
    have key : x1 * (h₁b * diagMat 2 b * h₂b) *
        (x2 * (h₁c * diagMat 2 (fun _ => c) * h₂c)) =
        x1 * h₁b * (diagMat 2 (pnatMul 2 b (fun _ => c)) * (h₂b * x2 * h₁c)) *
        h₂c := by
      calc x1 * (h₁b * diagMat 2 b * h₂b) *
          (x2 * (h₁c * diagMat 2 (fun _ => c) * h₂c))
          = x1 * h₁b * (diagMat 2 b * (h₂b * x2 * h₁c)) *
            (diagMat 2 (fun _ => c) * h₂c) := by group
        _ = x1 * h₁b * (diagMat 2 b * ((h₂b * x2 * h₁c) * diagMat 2 (fun _ => c))) *
            h₂c := by group
        _ = x1 * h₁b * (diagMat 2 b * (diagMat 2 (fun _ => c) * (h₂b * x2 * h₁c))) *
            h₂c := by rw [h_comm.symm]
        _ = x1 * h₁b * ((diagMat 2 b * diagMat 2 (fun _ => c)) * (h₂b * x2 * h₁c)) *
            h₂c := by group
        _ = x1 * h₁b * (diagMat 2 (pnatMul 2 b (fun _ => c)) * (h₂b * x2 * h₁c)) *
            h₂c := by rw [diagMat_mul]
    calc x1 * (h₁b * diagMat 2 b * h₂b) * (x2 * (h₁c * diagMat 2 (fun _ => c) * h₂c))
        = x1 * h₁b * (diagMat 2 (pnatMul 2 b (fun _ => c)) * (h₂b * x2 * h₁c)) * h₂c := key
      _ = x1 * h₁b * diagMat 2 (pnatMul 2 b (fun _ => c)) * (h₂b * x2 * h₁c * h₂c) := by group
  -- Step 4: T' equality
  apply HeckeRing.T'_ext (GL_pair 2)
  exact doubleCoset_eq_of_mem' _ _ h_product_mem

/-- m' for right-scalar: the multiplicity is 1. -/
private lemma m'_right_scalar_eq_one (b : Fin 2 → ℕ+) (hb : DivChain 2 b) (c : ℕ+)
    (hbc : DivChain 2 (pnatMul 2 b (fun _ => c))) :
    HeckeRing.m' (GL_pair 2)
      (T_diag 2 b hb) (T_diag 2 (fun _ => c) (divChain_const 2 c))
      (T_diag 2 (pnatMul 2 b (fun _ => c)) hbc) = 1 := by
  set D_b := T_diag 2 b hb
  set D_c := T_diag 2 (fun _ => c) (divChain_const 2 c)
  set D_bc := T_diag 2 (pnatMul 2 b (fun _ => c)) hbc
  have h_card : Fintype.card (decompQuot (GL_pair 2) D_c) = 1 := by
    have := T'_deg_scalar 2 c
    simp only [HeckeRing.T'_deg] at this; exact_mod_cast this
  haveI : Subsingleton (decompQuot (GL_pair 2) D_c) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_card)
  -- Upper bound: m' ≤ 1 (j unique from deg=1 of scalar, i from cancellation)
  have h_le : HeckeRing.m' (GL_pair 2) D_b D_c D_bc ≤ 1 := by
    classical
    simp only [HeckeRing.m']; norm_cast; rw [Nat.card_eq_fintype_card]
    apply Fintype.card_le_one_iff_subsingleton.mpr
    constructor; intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
    have hj : j₁ = j₂ := Subsingleton.elim j₁ j₂; subst hj
    simp only [Set.mem_setOf_eq] at h₁ h₂
    have hi : i₁ = i₂ := by
      by_contra hne
      apply HeckeRing.decompQuot_coset_diff (GL_pair 2) D_b i₁ i₂ hne
      -- Goal: {i₁.out * δ_b} * H = {i₂.out * δ_b} * H
      -- where δ_b = D_b.eql.choose
      -- From h₁, h₂ (with j₁ = j₂):
      --   {i₁.out * δ_b} * {j₁.out * δ_c} * H = {ξ} * H
      --   {i₂.out * δ_b} * {j₁.out * δ_c} * H = {ξ} * H
      set H' := (GL_pair 2).H with H'_def
      set δ_c := (D_c.eql.choose : GL (Fin 2) ℚ) with δ_c_def
      -- δ_c normalizes H: decompose δ_c via its double coset
      have hδc_mem : δ_c ∈
          DoubleCoset.doubleCoset (diagMat 2 (fun _ => c) : GL (Fin 2) ℚ) H' H' := by
        have h_spec := D_c.eql.choose_spec
        simp only [D_c, T_diag, T_mk, diagMat_delta] at h_spec
        rw [h_spec]; exact DoubleCoset.mem_doubleCoset_self H' H' _
      rw [DoubleCoset.mem_doubleCoset] at hδc_mem
      obtain ⟨h₁c, hh₁c, h₂c, hh₂c, hδc_eq⟩ := hδc_mem
      -- δ_c = (h₁c * h₂c) * diagMat(c) by scalar commutativity
      have hδc_simp : δ_c = (h₁c * h₂c) * diagMat 2 (fun _ => c) := by
        rw [hδc_eq, mul_assoc, diagMat_scalar_comm 2 c h₂c, ← mul_assoc]
      -- ConjAct δ_c • H = H
      have hδc_norm : ConjAct.toConjAct δ_c • H' = H' := by
        rw [hδc_simp, map_mul, MulAction.mul_smul, conjAct_scalar_smul_eq]
        exact HeckeRing.conjAct_smul_elt_eq H' ⟨h₁c * h₂c, H'.mul_mem hh₁c hh₂c⟩
      -- {δ_c} * H = H * {δ_c}
      have hδc_comm_H : ({δ_c} : Set (GL (Fin 2) ℚ)) * (H' : Set (GL (Fin 2) ℚ)) =
          (H' : Set (GL (Fin 2) ℚ)) * {δ_c} := by
        -- From hδc_norm: ConjAct.toConjAct δ_c • H' = H'
        -- This means δ_c normalizes H, so {δ_c} * H' * {δ_c⁻¹} = H'
        -- From hδc_norm: ConjAct.toConjAct δ_c • H' = H' means δ_c normalizes H'
        -- So {δ_c} * H' * {δ_c⁻¹} = H', which gives {δ_c} * H' = H' * {δ_c}
        have h_norm_coe : ({δ_c} : Set (GL (Fin 2) ℚ)) * (H' : Set (GL (Fin 2) ℚ)) * {δ_c⁻¹} =
            (H' : Set (GL (Fin 2) ℚ)) := by
          have h1 : (ConjAct.toConjAct δ_c • H' : Set (GL (Fin 2) ℚ)) = (H' : Set (GL (Fin 2) ℚ)) := by
            rw [show (ConjAct.toConjAct δ_c • H' : Set (GL (Fin 2) ℚ)) =
                ((ConjAct.toConjAct δ_c • H' : Subgroup _) : Set (GL (Fin 2) ℚ)) by rfl]
            congr 1
          rw [conjAct_smul_coe_eq] at h1
          exact h1
        have := congrFun (congrArg HMul.hMul h_norm_coe) {δ_c}
        simp_rw [mul_assoc, Set.singleton_mul_singleton] at this
        simpa using this
      -- τ_j ∈ H, so {τ_j * δ_c} * H = H * {δ_c}
      have hτ_mem : (j₁.out : GL (Fin 2) ℚ) ∈ H' := SetLike.coe_mem j₁.out
      have h_coset : ({(j₁.out : GL (Fin 2) ℚ) * δ_c} : Set _) * (H' : Set _) =
          (H' : Set _) * {δ_c} := by
        rw [← Set.singleton_mul_singleton, mul_assoc, hδc_comm_H, ← mul_assoc,
          Subgroup.singleton_mul_subgroup hτ_mem]
      -- Rewrite the m' condition using this
      have h12 := h₁.trans h₂.symm
      -- h12: {i₁.out * δ_b} * {j₁.out * δ_c} * H = {i₂.out * δ_b} * {j₁.out * δ_c} * H
      -- We need: {i₁.out * δ_b} * H = {i₂.out * δ_b} * H
      -- Strategy: show {j₁.out * δ_c} * H = H * {δ_c}, factor, right-cancel
      -- Rewrite using h_coset on both sides
      -- Use the fact that δ_c is D_c.eql.choose
      have h12' : ({(i₁.out : GL (Fin 2) ℚ) * D_b.eql.choose} : Set _) *
          ((H' : Set _) * {δ_c}) =
          ({(i₂.out : GL (Fin 2) ℚ) * D_b.eql.choose} : Set _) *
          ((H' : Set _) * {δ_c}) := by
        have lhs_eq : ({(i₁.out : GL (Fin 2) ℚ) * D_b.eql.choose} : Set _) *
            {(j₁.out : GL (Fin 2) ℚ) * δ_c} * (H' : Set _) =
            ({(i₁.out : GL (Fin 2) ℚ) * D_b.eql.choose} : Set _) *
            ((H' : Set _) * {δ_c}) := by
          rw [mul_assoc, h_coset]
        have rhs_eq : ({(i₂.out : GL (Fin 2) ℚ) * D_b.eql.choose} : Set _) *
            {(j₁.out : GL (Fin 2) ℚ) * δ_c} * (H' : Set _) =
            ({(i₂.out : GL (Fin 2) ℚ) * D_b.eql.choose} : Set _) *
            ((H' : Set _) * {δ_c}) := by
          rw [mul_assoc, h_coset]
        rw [← lhs_eq, ← rhs_eq]
        convert h12 using 2 <;> simp [H'_def, δ_c_def]
      -- Factor out {δ_c} on the right
      rw [← mul_assoc, ← mul_assoc] at h12'
      exact HeckeRing.mul_singleton_right_cancel δ_c _ _ h12'
    subst hi; rfl
  -- Lower bound: D_bc ∈ mulSupport gives m' ≠ 0, combined with m' ≥ 0 gives m' ≥ 1
  have h_pos : 0 < HeckeRing.m' (GL_pair 2) D_b D_c D_bc := by
    have h_mem : D_bc ∈ HeckeRing.mulSupport (GL_pair 2) D_b D_c := by
      simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
        true_and, Prod.exists]
      have ⟨i₀⟩ : Nonempty (decompQuot (GL_pair 2) D_b) :=
        Fintype.card_pos_iff.mp (by
          have := HeckeRing.T'_deg_pos (GL_pair 2) D_b
          simp only [HeckeRing.T'_deg] at this; omega)
      have ⟨j₀⟩ : Nonempty (decompQuot (GL_pair 2) D_c) :=
        Fintype.card_pos_iff.mp (by rw [h_card]; exact Nat.one_pos)
      exact ⟨i₀, j₀, mulMap_right_scalar_eq b hb c hbc (i₀, j₀)⟩
    have h_ne := HeckeRing.m'_pos_of_mem_mulSupport (GL_pair 2) D_b D_c D_bc h_mem
    have : (0 : ℤ) ≤ HeckeRing.m' (GL_pair 2) D_b D_c D_bc := by
      simp only [HeckeRing.m']; exact Nat.cast_nonneg _
    omega
  omega

/-- m' for right-scalar equals zero at non-target double cosets. -/
private lemma m'_right_scalar_eq_zero (b : Fin 2 → ℕ+) (hb : DivChain 2 b) (c : ℕ+)
    (hbc : DivChain 2 (pnatMul 2 b (fun _ => c)))
    (A : T' (GL_pair 2))
    (hA : A ≠ T_diag 2 (pnatMul 2 b (fun _ => c)) hbc) :
    HeckeRing.m' (GL_pair 2)
      (T_diag 2 b hb) (T_diag 2 (fun _ => c) (divChain_const 2 c)) A = 0 := by
  apply HeckeRing.m'_eq_zero_of_nmem_mulSupport
  intro h_mem
  simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
    true_and] at h_mem
  obtain ⟨⟨i, j⟩, heq⟩ := h_mem
  exact hA (heq.symm.trans (mulMap_right_scalar_eq b hb c hbc (i, j)))

/-- Right scalar multiplication: `T_elem(b) * T_elem(c,...,c) = T_elem(b·c)`.
    Mirror of `T_diag_scalar_mul`. -/
theorem T_elem_mul_scalar (b : Fin 2 → ℕ+) (hb : DivChain 2 b) (c : ℕ+) :
    T_elem 2 b hb * T_elem 2 (fun _ => c) (divChain_const 2 c) =
    T_elem 2 (pnatMul 2 b (fun _ => c))
      (DivChain_mul 2 b (fun _ => c) hb (divChain_const 2 c)) := by
  set D_b := T_diag 2 b hb
  set D_c := T_diag 2 (fun _ => c) (divChain_const 2 c)
  set D_bc := T_diag 2 (pnatMul 2 b (fun _ => c))
    (DivChain_mul 2 b (fun _ => c) hb (divChain_const 2 c))
  change HeckeRing.T_single (GL_pair 2) ℤ D_b 1 *
    HeckeRing.T_single (GL_pair 2) ℤ D_c 1 =
    HeckeRing.T_single (GL_pair 2) ℤ D_bc 1
  rw [HeckeRing.T_single_one_mul_T_single_one]
  apply Finsupp.ext; intro A
  simp only [HeckeRing.m, Finsupp.coe_mk, HeckeRing.T_single]
  by_cases h1 : A = D_bc
  · subst h1
    -- After subst, we need to show Finsupp.single D_bc 1 D_bc = 1
    -- This simplifies to the m' equality
    norm_num [Finsupp.single_apply]
    exact m'_right_scalar_eq_one b hb c
      (DivChain_mul 2 b (fun _ => c) hb (divChain_const 2 c))
  · -- When A ≠ D_bc, Finsupp.single D_bc 1 A = 0
    norm_num [Finsupp.single_apply, h1]
    exact m'_right_scalar_eq_zero b hb c
      (DivChain_mul 2 b (fun _ => c) hb (divChain_const 2 c)) A h1

/-- T(p,p) commutes with every T_elem. -/
lemma T_pp_comm_T_elem (a : Fin 2 → ℕ+) (ha : DivChain 2 a) :
    T_pp p hp * T_elem 2 a ha = T_elem 2 a ha * T_pp p hp := by
  unfold T_pp
  rw [T_diag_scalar_mul 2 ⟨p, hp.pos⟩ a ha, T_elem_mul_scalar a ha ⟨p, hp.pos⟩]
  exact (T_elem_congr_diag 2 (pnatMul_scalar_comm a ⟨p, hp.pos⟩) _ _).symm

/-- Powers of T(p,p): `T(p,p)^i = T(pⁱ, pⁱ)`. -/
lemma T_pp_pow (i : ℕ) :
    T_pp p hp ^ i =
    T_elem 2 (fun _ => ⟨p ^ i, pow_pos hp.pos i⟩) (divChain_const 2 _) := by
  induction i with
  | zero =>
    simp only [pow_zero]
    symm
    have heq : (fun (_ : Fin 2) => (⟨p ^ 0, pow_pos hp.pos 0⟩ : ℕ+)) =
        fun _ => (1 : ℕ+) :=
      funext fun _ => PNat.eq (by simp)
    exact (T_elem_congr_diag 2 heq _ _).trans T_elem_ones_eq
  | succ i ih =>
    rw [pow_succ', ih, T_pp]
    rw [T_diag_scalar_mul 2 ⟨p, hp.pos⟩ (fun _ => ⟨p ^ i, pow_pos hp.pos i⟩)
      (divChain_const 2 _)]
    exact T_elem_congr_diag 2
      (funext fun _ => PNat.eq (by simp [pnatMul_val, pow_succ, mul_comm]))
      _ _

/-- The divisor pairs of pᵏ with a|d are (pⁱ, p^{k-i}) for i ≤ k/2. -/
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
        (not_le_of_lt (Nat.pow_lt_pow_right hp.one_lt (by omega))))])).symm

end Structural

end HeckeRing.GL2
