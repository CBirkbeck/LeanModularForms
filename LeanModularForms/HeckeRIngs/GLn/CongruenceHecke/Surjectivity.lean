/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.DegreeCombinatorics

/-!
# Hecke Ring for Congruence Subgroups (Shimura §3.3) — Surjectivity (Theorem 3.35)

The capstone of the chain: coprime/bad-prime multiplicativity
(`T_coprime_mul`, `T_coprime_mul`-companions), algebraic independence of the
generators (`T_gen_algebraicIndependent`, `π_injective`, `ker_π_le_ker_ψ`), the
`ψ`-range computations (`T_diag_mem_ψ_range`, `ψ_surjective`), and the assembly
of the surjective ring homomorphism `shimura_ring_hom` proving
**Shimura Theorem 3.35**: `R(Γ, Δ) ↠ R(Γ₀(N), Δ₀(N))`.

## Main results

* `shimura_thm_3_35` — the surjection `R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N))`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.3
-/

open Matrix Subgroup.Commensurable Pointwise Matrix.SpecialLinearGroup

open scoped Pointwise MatrixGroups

namespace HeckeRing.GLn

variable (N : ℕ) [NeZero N]
/-- **Coprime diagonal multiplication for Gamma0** (Shimura §3.2, Prop 3.16–17):
`T'(1,m) * T'(1,n) = T'(1,mn)` when `gcd(m, n) = 1`.

Partners `T_bad_mul` (for m, n ∣ N^∞). Together they give the full
multiplicativity needed for `ker_π_le_ker_ψ`. -/
private theorem T_coprime_mul (N : ℕ) [NeZero N]
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n) (hcop : Nat.Coprime m n) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m])
        (fun i => by fin_cases i <;> simp [hm_pos]) (by simp [Int.gcd_one_left])) 1 *
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, n])
        (fun i => by fin_cases i <;> simp [hn_pos]) (by simp [Int.gcd_one_left])) 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m * n])
        (fun i => by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
        (by simp [Int.gcd_one_left])) 1 := by
  refine HeckeRing.T_single_one_mul_eq_single (Gamma0_pair N) _ _ _ (by
    set D₁ := T_diag_Gamma0 N (![1, m]) (fun i => by fin_cases i <;> simp [hm_pos])
      (by simp [Int.gcd_one_left])
    set D₂ := T_diag_Gamma0 N (![1, n]) (fun i => by fin_cases i <;> simp [hn_pos])
      (by simp [Int.gcd_one_left])
    set D_out := T_diag_Gamma0 N (![1, m * n])
      (fun i => by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
      (by simp [Int.gcd_one_left])
    set μ := HeckeRing.heckeMultiplicity (Gamma0_pair N) D₁.rep D₂.rep D_out.rep
    have h_mulMap : ∀ p, HeckeRing.mulMap (Gamma0_pair N) D₁.rep D₂.rep p = D_out :=
      mulMap_Gamma0_coprime_eq N m n hm_pos hn_pos hcop
    have h_zero_all : ∀ A, A ≠ D_out →
        (HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep) A = 0 := by
      intro A hA; simp only [HeckeRing.m_apply]
      exact HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique
        (Gamma0_pair N) _ _ D_out A hA h_mulMap
    have h_m_eq : HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep =
        Finsupp.single D_out μ := by
      ext A; simp only [Finsupp.single_apply]
      split_ifs with h
      · subst h; simp only [HeckeRing.m_apply]; rfl
      · exact h_zero_all A (Ne.symm h)
    have h_deg_mul := Gamma0_deg_coprime_mul N m n hm_pos hn_pos hcop
    have h_deg_prod : HeckeRing.deg (Gamma0_pair N)
        (HeckeRing.T_single _ ℤ D₁ 1 * HeckeRing.T_single _ ℤ D₂ 1) =
        HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out := by
      rw [HeckeRing.deg_mul, HeckeRing.deg_T_single, HeckeRing.deg_T_single,
        one_mul, one_mul, h_deg_mul]
    have h_deg_m_eq : HeckeRing.deg (Gamma0_pair N)
        (HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep) =
        μ * HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out := by
      rw [h_m_eq]; simp [HeckeRing.deg_T_single]
    rw [HeckeRing.T_single_one_mul_T_single_one] at h_deg_prod
    have hd_out_pos : (0 : ℤ) < HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out :=
      HeckeRing.HeckeCoset_deg_pos (Gamma0_pair N) D_out
    have hd_out_ne : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out ≠ 0 :=
      ne_of_gt hd_out_pos
    exact mul_right_cancel₀ hd_out_ne (by linarith [h_deg_prod, h_deg_m_eq])) ?_
  · intro A hA
    exact HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique (Gamma0_pair N) _ _ _ A hA
      (mulMap_Gamma0_coprime_eq N m n hm_pos hn_pos hcop)

/-- **Coprime Finsupp coefficient factorisation**: for Hecke algebra elements
`f, g` whose support cosets have pairwise coprime diagonal products, the
Finsupp coefficient at `T_diag(d₁ * d₂)` factors as `f(d₁) * g(d₂)`.

This is the inductive bridge for `multi_prime_kronecker`.
Proof: expand `(f * g)(D)` via `mul_def` / `Finsupp.sum`, apply
`T_diag_mul_coprime` to each coprime pair to get
`m(rep D₁, rep D₂) = single(T_diag(a*b), 1)`, then `diagonal_representative_unique`
collapses the double sum to the unique pair `(d₁, d₂)` via `huniq`. -/
private lemma coprime_mul_coeff (f g : HeckeAlgebra 2)
    (d₁ d₂ : Fin 2 → ℕ)
    (hd₁_pos : ∀ i, 0 < d₁ i) (hd₂_pos : ∀ i, 0 < d₂ i)
    (hd₁_div : DivChain 2 d₁) (hd₂_div : DivChain 2 d₂)
    (hf_diag : ∀ D, f D ≠ 0 → ∃ a, D = T_diag a ∧ (∀ i, 0 < a i) ∧ DivChain 2 a)
    (hg_diag : ∀ D, g D ≠ 0 → ∃ b, D = T_diag b ∧ (∀ i, 0 < b i) ∧ DivChain 2 b)
    (hcop_pair : ∀ D₁ D₂ a b, f D₁ ≠ 0 → g D₂ ≠ 0 →
      D₁ = T_diag a → D₂ = T_diag b →
      (∀ i, 0 < a i) → (∀ i, 0 < b i) → DivChain 2 a → DivChain 2 b →
      Nat.Coprime (∏ i, a i) (∏ i, b i))
    (huniq : ∀ D₁ D₂ a b, f D₁ ≠ 0 → g D₂ ≠ 0 →
      D₁ = T_diag a → D₂ = T_diag b →
      (∀ i, 0 < a i) → (∀ i, 0 < b i) → DivChain 2 a → DivChain 2 b →
      Nat.Coprime (∏ i, a i) (∏ i, b i) →
      T_diag (a * b) = T_diag (d₁ * d₂) → a = d₁ ∧ b = d₂) :
    (f * g) (T_diag (d₁ * d₂)) = f (T_diag d₁) * g (T_diag d₂) := by
  set D := T_diag (d₁ * d₂) with hD_def
  have hm_delta : ∀ D₁ D₂ : HeckeCoset (GL_pair 2),
      f D₁ ≠ 0 → g D₂ ≠ 0 →
      (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D =
      if D₁ = T_diag d₁ ∧ D₂ = T_diag d₂ then 1 else 0 := by
    intro D₁ D₂ hD₁ hD₂
    obtain ⟨a, rfl, ha_pos, ha_div⟩ := hf_diag D₁ hD₁
    obtain ⟨b, rfl, hb_pos, hb_div⟩ := hg_diag D₂ hD₂
    have hcop_ab := hcop_pair _ _ a b hD₁ hD₂ rfl rfl ha_pos hb_pos ha_div hb_div
    have hm_eq : HeckeRing.m (GL_pair 2) (HeckeCoset.rep (T_diag a))
        (HeckeCoset.rep (T_diag b)) = Finsupp.single (T_diag (a * b)) 1 := by
      rw [← HeckeRing.T_single_one_mul_T_single_one]
      exact T_diag_mul_coprime 2 a b ha_pos hb_pos ha_div hb_div hcop_ab
    rw [hm_eq, Finsupp.single_apply, hD_def]
    congr 1; apply propext
    exact ⟨fun h => by
        have ⟨ha, hb⟩ := huniq _ _ a b hD₁ hD₂ rfl rfl ha_pos hb_pos ha_div hb_div hcop_ab h
        exact ⟨congr_arg T_diag ha, congr_arg T_diag hb⟩,
      fun ⟨ha, hb⟩ => by
        rw [diagonal_representative_unique 2 a d₁ ha_pos hd₁_pos ha_div hd₁_div ha,
            diagonal_representative_unique 2 b d₂ hb_pos hd₂_pos hb_div hd₂_div hb]⟩
  have h_expand : (f * g) D = ∑ D₁ ∈ f.support, ∑ D₂ ∈ g.support,
      f D₁ * g D₂ * (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂)) D := by
    show (Finsupp.sum f (fun D₁ b₁ => Finsupp.sum g (fun D₂ b₂ =>
      b₁ • b₂ • HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂)))) D = _
    simp only [Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      smul_eq_mul, mul_assoc]
  rw [h_expand]
  conv_lhs =>
    arg 2; ext D₁; arg 2; ext D₂
    rw [show f D₁ * g D₂ * (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂)) D =
        if D₁ = T_diag d₁ ∧ D₂ = T_diag d₂ then f D₁ * g D₂ else 0 from by
      by_cases hD₁ : f D₁ = 0
      · simp [hD₁]
      · by_cases hD₂ : g D₂ = 0
        · simp [hD₂]
        · rw [hm_delta D₁ D₂ hD₁ hD₂, mul_ite, mul_one, mul_zero]]
  have h_inner : ∀ D₁ ∈ f.support, (∑ D₂ ∈ g.support,
      if D₁ = T_diag d₁ ∧ D₂ = T_diag d₂ then f D₁ * g D₂ else 0) =
      if D₁ = T_diag d₁ then f D₁ * g (T_diag d₂) else 0 := by
    intro D₁ _
    by_cases h : D₁ = T_diag d₁
    · subst h; simp only [true_and]
      rw [Finset.sum_ite_eq']; split_ifs with hm
      · rfl
      · simp [Finsupp.notMem_support_iff.mp hm]
    · simp [h]
  rw [Finset.sum_congr rfl h_inner, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · simp [Finsupp.notMem_support_iff.mp hm]

-- `det_SLnZ_eq_one`, `det_doubleCoset_eq`, `prod_rep_T_diag`, `det_mulMap_eq`,
-- `T_gen_pow_support_qpower`, `T_gen_pow_entries_qpower`, `support_mul_exists`
-- moved to `LeanModularForms.HeckeRIngs.GLn.PolynomialRing` (namespace
-- `HeckeRing.GLn.Inj`). Opened here for use in downstream lemmas.
open HeckeRing.GLn.Inj
  (T_gen_pow_support_qpower T_gen_pow_entries_qpower support_mul_exists
   det_SLnZ_eq_one det_doubleCoset_eq prod_rep_T_diag det_mulMap_eq)

/-- **Shimura Proposition 3.31 (Surjectivity)**: Every GL₂(ℤ)-double coset has a
    `Γ₀(N)`-double coset preimage under `cosetMap`. Combined with `shimura_prop_3_31`
    (injectivity on coprime-det cosets), this gives the bijection between coprime-det
    cosets at the two levels — Shimura's full Prop 3.31.

    **Proof**: Apply `exists_diagonal_representative` to get a diagonal form
    `(a₀, a₁)` for the GL coset. The coprime-det condition gives `gcd(a₀, N) = 1`,
    so `T_diag_Gamma0 N (![a₀, a₁])` is a valid `Γ₀(N)` coset whose `cosetMap`
    image equals the original coset via `cosetMap_T_diag_Gamma0`. -/
private theorem shimura_prop_3_31_surjective (N : ℕ) [NeZero N]
    (D : HeckeCoset (GL_pair 2))
    (hD_coprime : Int.gcd
      ((↑((HeckeCoset.rep D : (GL_pair 2).Δ) : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ).det.num) N = 1) :
    ∃ (D' : HeckeCoset (Gamma0_pair N)), cosetMap N D' = D := by
  obtain ⟨a, ha_pos, _ha_div, ha_eq⟩ := exists_diagonal_representative 2 (HeckeCoset.rep D)
  have hD_eq : D = T_diag a := by
    rw [show D = (⟦HeckeCoset.rep D⟧ : HeckeCoset (GL_pair 2)) from
      (HeckeCoset.mk_rep D).symm, ha_eq]
  have hrep_eq : (HeckeCoset.rep D : (GL_pair 2).Δ) =
      (HeckeCoset.rep (T_diag a) : (GL_pair 2).Δ) := by
    rw [hD_eq]
  rw [hrep_eq] at hD_coprime
  rw [prod_rep_T_diag a ha_pos] at hD_coprime
  simp only [Fin.prod_univ_two] at hD_coprime
  have ha0_gcd : Int.gcd (a 0 : ℤ) N = 1 := by
    have h_num : (((a 0 : ℚ) * (a 1 : ℚ)).num) = (a 0 * a 1 : ℤ) := by
      have : ((a 0 : ℚ) * (a 1 : ℚ)) = ((a 0 * a 1 : ℕ) : ℚ) := by push_cast; ring
      rw [this]; exact_mod_cast Rat.num_natCast _
    rw [h_num] at hD_coprime
    have hNat : Nat.Coprime (a 0 * a 1) N := by
      show (a 0 * a 1).gcd N = 1
      have h_push : (↑(a 0 * a 1 : ℕ) : ℤ).gcd ↑N = (a 0 * a 1).gcd N :=
        Int.gcd_natCast_natCast _ _
      rw [← h_push]; push_cast; exact hD_coprime
    have : (a 0).gcd N = 1 := Nat.Coprime.coprime_dvd_left ⟨a 1, rfl⟩ hNat
    exact_mod_cast this
  refine ⟨T_diag_Gamma0 N a ha_pos ha0_gcd, ?_⟩
  rw [cosetMap_T_diag_Gamma0, ← hD_eq]

/-- Determinant multiplicativity for Hecke products: if all support cosets of `f`
have `det = d₁` and all of `g` have `det = d₂`, then all support cosets of
`f * g` have `det = d₁ * d₂`. Uses `support_mul_exists` + `det_mulMap_eq`. -/
private lemma support_det_mul (f g : HeckeAlgebra 2) (d₁ d₂ : ℚ)
    (hf : ∀ D, f D ≠ 0 →
      (↑(↑(HeckeCoset.rep D) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = d₁)
    (hg : ∀ D, g D ≠ 0 →
      (↑(↑(HeckeCoset.rep D) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = d₂)
    (D : HeckeCoset (GL_pair 2)) (hD : (f * g) D ≠ 0) :
    (↑(↑(HeckeCoset.rep D) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = d₁ * d₂ := by
  obtain ⟨D₁, D₂, hfD₁, hgD₂, hD_mem⟩ := support_mul_exists f g D hD
  rw [HeckeRing.mulSupport, Finset.mem_image] at hD_mem
  obtain ⟨p, _, hD_eq⟩ := hD_mem
  rw [← hD_eq, det_mulMap_eq, hf D₁ hfD₁, hg D₂ hgD₂]

/-- Multi-prime determinant tracking (det version): support of `∏_{S} T_gen(p)^{e_p}`
has `det(rep D) = ∏_{S} p^{e_p 0 + 2*e_p 1}`. Proved by `Finset.induction` using
`support_det_mul` + `T_gen_pow_support_qpower`. -/
private lemma prod_gen_det_eq (S : Finset {p : ℕ // p.Prime})
    (e : {p : ℕ // p.Prime} → Fin 2 → ℕ) :
    ∀ D : HeckeCoset (GL_pair 2),
    (∏ p ∈ S, (T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1))) D ≠ 0 →
    (↑(↑(HeckeCoset.rep D) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
    ↑(∏ p ∈ S, p.1 ^ (e p 0 + 2 * e p 1) : ℕ) := by
  induction S using Finset.induction with
  | empty =>
    intro D hD
    simp only [Finset.prod_empty] at hD ⊢
    rw [HeckeRing.one_def (GL_pair 2) (Z := ℤ)] at hD
    have hD_eq : D = HeckeCoset.one (GL_pair 2) := by
      by_contra hne
      apply hD
      show (HeckeRing.T_single (GL_pair 2) ℤ (HeckeCoset.one (GL_pair 2)) 1) D = 0
      show (Finsupp.single (HeckeCoset.one (GL_pair 2)) 1) D = 0
      rw [Finsupp.single_apply, if_neg (Ne.symm hne)]
    rw [hD_eq, show (HeckeCoset.one (GL_pair 2) : HeckeCoset (GL_pair 2)) =
      T_diag (fun _ : Fin 2 => 1) from T_diag_ones.symm,
      prod_rep_T_diag _ (fun _ => Nat.one_pos)]
    simp [Fin.prod_univ_two]
  | @insert q' S'' hq'' ih =>
    intro D hD
    rw [Finset.prod_insert hq''] at hD
    have h := support_det_mul _ _
      (↑(q'.1 ^ (e q' 0 + 2 * e q' 1) : ℕ) : ℚ)
      (↑(∏ p ∈ S'', p.1 ^ (e p 0 + 2 * e p 1) : ℕ) : ℚ)
      (fun D' hD' => by
        obtain ⟨a, hDa, ha_pos, _, ha_det⟩ := T_gen_pow_support_qpower q' (e q') D' hD'
        rw [hDa, prod_rep_T_diag a ha_pos]
        exact_mod_cast ha_det)
      (fun D' hD' => ih D' hD')
      D hD
    rw [h]; push_cast [Finset.prod_insert hq'']; ring

/-- Multi-prime support tracking: every coset in the support of
`∏_{p ∈ S} T_gen(p)^{e_p}` has diagonal product `∏_{p ∈ S} p^{e_p 0 + 2*e_p 1}`. -/
private lemma prod_gen_support_det (S : Finset {p : ℕ // p.Prime})
    (e : {p : ℕ // p.Prime} → Fin 2 → ℕ) (D : HeckeCoset (GL_pair 2))
    (hD : (∏ p ∈ S, (T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1))) D ≠ 0) :
    ∃ a, D = T_diag a ∧ (∀ i, 0 < a i) ∧ DivChain 2 a ∧
      (∏ i, a i) = ∏ p ∈ S, p.1 ^ (e p 0 + 2 * e p 1) := by
  obtain ⟨a, ha_pos, ha_div, ha_eq⟩ := exists_diagonal_representative 2 (HeckeCoset.rep D)
  have hD_eq : D = T_diag a := by rw [← Quotient.out_eq D]; exact ha_eq
  refine ⟨a, hD_eq, ha_pos, ha_div, ?_⟩
  have h_det := prod_gen_det_eq S e D hD
  rw [hD_eq, prod_rep_T_diag a ha_pos] at h_det
  exact_mod_cast h_det

/-- **Multi-prime coefficient factorisation**: the Finsupp coefficient of a product
of per-prime generator monomials at a product of per-prime cosets factors as the
product of per-prime coefficients.

Proof by `Finset.induction` on `S`, using `coprime_mul_coeff` at each step
to peel off one prime. -/
private lemma multi_prime_coeff_factor (S : Finset {p : ℕ // p.Prime})
    (e d : {p : ℕ // p.Prime} → Fin 2 → ℕ) :
    (∏ p ∈ S, (T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1)))
      (T_diag (∏ p ∈ S, ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1])) =
    ∏ p ∈ S, (T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1))
      (T_diag (ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1])) := by
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    rw [HeckeRing.one_def (GL_pair 2) (Z := ℤ)]
    show (Finsupp.single (HeckeCoset.one (GL_pair 2)) (1 : ℤ)) (T_diag 1) = 1
    rw [Finsupp.single_apply, if_pos]
    show HeckeCoset.one (GL_pair 2) = T_diag 1
    exact T_diag_ones.symm
  | @insert q S' hq ih =>
    rw [Finset.prod_insert hq, Finset.prod_insert hq, Finset.prod_insert hq]
    set f := T_gen 2 q.1 0 ^ (e q 0) * T_gen 2 q.1 1 ^ (e q 1)
    set g := ∏ p ∈ S', T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1)
    set d₁ := ppowDiag 2 q.1 ![d q 1, d q 0 + d q 1]
    set d₂ := ∏ p ∈ S', ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1]
    have h_factor : (f * g) (T_diag (d₁ * d₂)) = f (T_diag d₁) * g (T_diag d₂) := by
      have hd₁_div_proof : DivChain 2 d₁ :=
        divChain_ppow 2 q.1 _ (by
          intro i j h
          fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def] <;> omega)
      have hd₂_div_proof : DivChain 2 d₂ :=
        Finset.prod_induction _ (DivChain 2)
          (fun a b ha hb => DivChain_mul 2 a b ha hb)
          (fun _ _ => dvd_refl 1)
          (fun (p : {p : ℕ // p.Prime}) _ => divChain_ppow 2 p.1 _ (by
            intro i j h
            fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def] <;> omega))
      have hd₂_pos_proof : ∀ i, 0 < d₂ i := fun i => by
        show 0 < d₂ i
        simp only [d₂, Finset.prod_apply]
        exact Finset.prod_pos
          (fun (p : {p : ℕ // p.Prime}) _ => ppowDiag_pos 2 p.1 p.2 _ i)
      have h_diag_of_support : ∀ D : HeckeCoset (GL_pair 2), (f D ≠ 0 ∨ g D ≠ 0) →
          ∃ a, D = T_diag a ∧ (∀ i, 0 < a i) ∧ DivChain 2 a := by
        intro D _
        obtain ⟨a, ha_pos, ha_div, ha_eq⟩ :=
          exists_diagonal_representative 2 (HeckeCoset.rep D)
        refine ⟨a, ?_, ha_pos, ha_div⟩
        rw [← Quotient.out_eq D]; exact ha_eq
      refine coprime_mul_coeff f g d₁ d₂
        (ppowDiag_pos 2 q.1 q.2 _)
        hd₂_pos_proof
        hd₁_div_proof
        hd₂_div_proof
        (fun D hD => h_diag_of_support D (Or.inl hD))
        (fun D hD => h_diag_of_support D (Or.inr hD))
        ?_ -- hcop_pair
        ?_ -- huniq
      · intro D₁ D₂ a b hfD₁ hgD₂ hD₁_eq hD₂_eq ha_pos hb_pos ha_div hb_div
        obtain ⟨a', hDa'_eq, ha'_pos, ha'_div, ha'_det⟩ :=
          T_gen_pow_support_qpower q (e q) D₁ hfD₁
        have ha_eq : a = a' := diagonal_representative_unique 2 a a' ha_pos ha'_pos ha_div ha'_div
          (hD₁_eq ▸ hDa'_eq)
        subst ha_eq; rw [ha'_det]
        obtain ⟨b', hDb', hb'_pos, hb'_div, hb'_det⟩ := prod_gen_support_det S' e D₂ hgD₂
        have hb_eq : b = b' := diagonal_representative_unique 2 b b' hb_pos hb'_pos hb_div hb'_div
          (hD₂_eq ▸ hDb')
        subst hb_eq; rw [hb'_det]
        apply Nat.Coprime.pow_left
        apply Nat.coprime_prod_right_iff.mpr
        intro p hp
        apply Nat.Coprime.pow_right
        exact (Nat.coprime_primes q.2 p.2).mpr (fun h => hq (by rw [Subtype.ext h]; exact hp))
      · intro D₁ D₂ a b hfD₁ hgD₂ hD₁_eq hD₂_eq ha_pos hb_pos ha_div hb_div hcop h_eq
        have hd₁_div_proof : DivChain 2 d₁ :=
          divChain_ppow 2 q.1 _ (by
            intro i j h
            fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def] <;> omega)
        have hd₂_div_proof : DivChain 2 d₂ :=
          Finset.prod_induction _ (DivChain 2)
            (fun x y => DivChain_mul 2 x y)
            (fun _ _ => dvd_refl 1)
            (fun (p : {p : ℕ // p.Prime}) _ => divChain_ppow 2 p.1 _ (by
              intro i j h
              fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def] <;> omega))
        have hd₂_pos_proof : ∀ i, 0 < d₂ i := fun i => by
          show 0 < d₂ i
          simp only [d₂, Finset.prod_apply]
          exact Finset.prod_pos
            (fun (p : {p : ℕ // p.Prime}) _ => ppowDiag_pos 2 p.1 p.2 _ i)
        have hab := diagonal_representative_unique 2 (a * b) (d₁ * d₂)
          (pi_mul_pos 2 a b ha_pos hb_pos)
          (pi_mul_pos 2 d₁ d₂ (ppowDiag_pos 2 q.1 q.2 _) hd₂_pos_proof)
          (DivChain_mul 2 a b ha_div hb_div)
          (DivChain_mul 2 d₁ d₂ hd₁_div_proof hd₂_div_proof)
          h_eq
        have ha_qpow := T_gen_pow_entries_qpower q (e q) D₁ hfD₁ a hD₁_eq ha_pos ha_div
        obtain ⟨b', hDb'_eq, hb'_pos, hb'_div, hb'_det⟩ := prod_gen_support_det S' e D₂ hgD₂
        have hb_eq' : b = b' := diagonal_representative_unique 2 b b' hb_pos hb'_pos hb_div hb'_div
          (hD₂_eq ▸ hDb'_eq)
        subst hb_eq'
        have hcop_q_S'_prod : Nat.Coprime q.1 (∏ p ∈ S', p.1 ^ (e p 0 + 2 * e p 1)) := by
          apply Nat.coprime_prod_right_iff.mpr
          intro p hp
          apply Nat.Coprime.pow_right
          exact (Nat.coprime_primes q.2 p.2).mpr
            (fun h_eq_p => hq (by rw [show q = p from Subtype.ext h_eq_p]; exact hp))
        have entry_eq : ∀ i, a i = d₁ i := by
          intro i
          have h_i : a i * b i = d₁ i * d₂ i := by
            have := congr_fun hab i; simp only [Pi.mul_apply] at this; exact this
          -- q ∤ b(i) since ∏ b = ∏_{S'} p^{...} coprime to q
          have hq_not_dvd_b : ¬(q.1 ∣ b i) := by
            intro hdvd
            apply (Nat.Prime.coprime_iff_not_dvd q.2).mp hcop_q_S'_prod
            rw [← hb'_det]
            exact dvd_trans hdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
          have hcop_a_b : Nat.Coprime (a i) (b i) := by
            rw [Nat.coprime_iff_gcd_eq_one]
            by_contra hne
            obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hne
            have hp_dvd_a : p ∣ a i := dvd_trans hp_dvd (Nat.gcd_dvd_left _ _)
            have hp_dvd_b : p ∣ b i := dvd_trans hp_dvd (Nat.gcd_dvd_right _ _)
            by_cases hpq : p = q.1
            · exact hq_not_dvd_b (hpq ▸ hp_dvd_b)
            · exact ha_qpow p hp_prime hpq i hp_dvd_a
          have hq_not_dvd_d₂ : ¬(q.1 ∣ d₂ i) := by
            intro hdvd
            change q.1 ∣ (∏ p ∈ S', ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1]) i at hdvd
            rw [Finset.prod_apply] at hdvd
            rcases (q.2.prime.dvd_finset_prod_iff _).mp hdvd with ⟨p, hp_mem, hp_dvd⟩
            simp only [ppowDiag] at hp_dvd
            have hqp : q.1 = p.1 :=
              (Nat.prime_dvd_prime_iff_eq q.2 p.2).mp (q.2.dvd_of_dvd_pow hp_dvd)
            exact hq (Subtype.ext hqp ▸ hp_mem)
          have hcop_a_d₂ : Nat.Coprime (a i) (d₂ i) := by
            rw [Nat.coprime_iff_gcd_eq_one]
            by_contra hne
            obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hne
            have hp_dvd_a : p ∣ a i := dvd_trans hp_dvd (Nat.gcd_dvd_left _ _)
            have hp_dvd_d₂ : p ∣ d₂ i := dvd_trans hp_dvd (Nat.gcd_dvd_right _ _)
            by_cases hpq : p = q.1
            · exact hq_not_dvd_d₂ (hpq ▸ hp_dvd_d₂)
            · exact ha_qpow p hp_prime hpq i hp_dvd_a
          have ha_dvd_d₁ : a i ∣ d₁ i :=
            (Nat.Coprime.dvd_of_dvd_mul_right hcop_a_d₂ (h_i ▸ dvd_mul_right _ _))
          have hcop_d₁_b : Nat.Coprime (d₁ i) (b i) := by
            show Nat.Coprime (ppowDiag 2 q.1 ![d q 1, d q 0 + d q 1] i) (b i)
            simp only [ppowDiag]
            exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd q.2).mpr hq_not_dvd_b)
          have hd₁_dvd_a : d₁ i ∣ a i :=
            (Nat.Coprime.dvd_of_dvd_mul_right hcop_d₁_b (h_i.symm ▸ dvd_mul_right _ _))
          exact Nat.dvd_antisymm ha_dvd_d₁ hd₁_dvd_a
        refine ⟨funext entry_eq, funext fun i => ?_⟩
        have h_i : a i * b i = d₁ i * d₂ i := by
          have := congr_fun hab i; simp only [Pi.mul_apply] at this; exact this
        exact Nat.eq_of_mul_eq_mul_left (ha_pos i) (entry_eq i ▸ h_i)
    rw [h_factor, ih]

/-- **Algebraic independence of Hecke generators**: the generators `T_gen 2 p k`
for all primes `p` and `k ∈ Fin 2` are algebraically independent over `ℤ`.
Equivalently, the presentation map `π_hom` is injective.

**Proof**: follows the same "minimum-support Kronecker extraction" pattern as
`evalHom_injective_two` (PolynomialRing.lean), extended to multi-prime monomials
via `multi_prime_kronecker`. For any nonzero `f`, pick the monomial `s` in `f.support`
that minimises `(s(p₁,1), s(p₂,1), …)` lexicographically; evaluating `π_hom(f)`
at the leading coset of `s` extracts `f.coeff s ≠ 0`. -/
-- Helper: convert a GenIdx →₀ ℕ exponent into per-prime exponents
private noncomputable def toPrimeExp (d : GenIdx →₀ ℕ) : {p : ℕ // p.Prime} → Fin 2 → ℕ :=
  fun p k => d (p, k)

-- Helper: the set of primes appearing in a monomial
private def primesOf (d : GenIdx →₀ ℕ) : Finset {p : ℕ // p.Prime} :=
  d.support.image Prod.fst

/-- The monomial evaluation `∏ T_gen(i)^{d(i)}` equals the per-prime-grouped product
`∏_{p ∈ primesOf d} (T_gen(p,0)^{d(p,0)} * T_gen(p,1)^{d(p,1)})`.
This is a rearrangement of a commutative product. -/
private lemma monomial_eval_eq_prod_primes (d : GenIdx →₀ ℕ) :
    (∏ i ∈ d.support, (fun j : GenIdx => T_gen 2 j.1.1 j.2) i ^ d i) =
    ∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
      T_gen 2 p.1 1 ^ (toPrimeExp d p 1)) := by
  rw [← Finset.prod_fiberwise_of_maps_to
    (g := Prod.fst) (t := primesOf d)
    (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)]
  congr 1; ext p; congr 1
  set S := Finset.univ.image (fun k : Fin 2 => (p, k)) with hS_def
  rw [show T_gen 2 (↑p) 0 ^ toPrimeExp d p 0 * T_gen 2 (↑p) 1 ^ toPrimeExp d p 1 =
    ∏ i ∈ S, (fun j : GenIdx => T_gen 2 (↑j.1) j.2) i ^ d i from by
      simp [S, Fin.prod_univ_two, toPrimeExp, Finset.prod_image (fun
        (_ : Fin 2) _ (_ : Fin 2) _ h => Prod.mk.injEq _ _ _ _ |>.mp h |>.2)]]
  refine Finset.prod_subset (M := HeckeAlgebra 2) ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hi
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨i.2, Prod.ext hi.2.symm rfl⟩
  · intro i hiS hi_not
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, not_and] at hi_not
    have hi_fst : i.1 = p := by
      simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hiS
      obtain ⟨k, hk⟩ := hiS
      exact hk ▸ rfl
    have h_zero : d i = 0 := by
      by_contra hne
      exact hi_not hne hi_fst
    rw [h_zero]; exact pow_zero _

/-- The diagonal product of `∏ ppowDiag` equals the per-prime determinant product. -/
private lemma prod_ppowDiag_eq (S : Finset {p : ℕ // p.Prime})
    (e : {p : ℕ // p.Prime} → Fin 2 → ℕ) :
    ∏ i, (∏ p ∈ S, ppowDiag 2 p.1 ![e p 1, e p 0 + e p 1]) i =
    ∏ p ∈ S, p.1 ^ (e p 0 + 2 * e p 1) := by
  simp only [Finset.prod_apply]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p _
  simp only [ppowDiag, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ← pow_add]
  congr 1; omega

/-- For monomial d, if the per-prime determinant profile differs from s's,
the evaluation at s's leading coset is 0.  Uses `prod_gen_support_det`. -/
private lemma monomial_eval_zero_of_det_ne (d s : GenIdx →₀ ℕ)
    (h_det : ∏ p ∈ primesOf d, p.1 ^ (toPrimeExp d p 0 + 2 * toPrimeExp d p 1) ≠
             ∏ p ∈ primesOf s, p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1)) :
    (∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
      T_gen 2 p.1 1 ^ (toPrimeExp d p 1)))
      (T_diag (∏ p ∈ primesOf s, ppowDiag 2 p.1
        ![toPrimeExp s p 1, toPrimeExp s p 0 + toPrimeExp s p 1])) = 0 := by
  by_contra h; push_neg at h
  apply h_det
  obtain ⟨a, ha_eq, ha_pos, ha_div, ha_det⟩ := prod_gen_support_det (primesOf d) (toPrimeExp d)
    (T_diag _) (by rwa [ne_eq] at h)
  set c := ∏ p ∈ primesOf s, ppowDiag 2 p.1 ![toPrimeExp s p 1, toPrimeExp s p 0 + toPrimeExp s p 1]
  have hc_pos : ∀ i, 0 < c i := fun i => by
    show 0 < c i
    simp only [c, Finset.prod_apply]
    exact Finset.prod_pos
      (fun (p : {p : ℕ // p.Prime}) _ => ppowDiag_pos 2 p.1 p.2 _ i)
  have hc_div : DivChain 2 c := Finset.prod_induction _ (DivChain 2)
    (fun a b ha hb => DivChain_mul 2 a b ha hb) (fun _ _ => dvd_refl 1)
    (fun (p : {p : ℕ // p.Prime}) _ => divChain_ppow 2 p.1 _ (by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def] <;> omega))
  have hc_prod : ∏ i, c i = ∏ p ∈ primesOf s, p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1) :=
    prod_ppowDiag_eq (primesOf s) (toPrimeExp s)
  have hac := diagonal_representative_unique 2 a c ha_pos hc_pos ha_div hc_div ha_eq.symm
  rw [hac] at ha_det; rw [← ha_det, ← hc_prod]


private lemma T_gen_algebraicIndependent :
    AlgebraicIndependent ℤ (fun i : GenIdx => T_gen 2 i.1.1 i.2) := by
  rw [algebraicIndependent_iff_injective_aeval]
  show Function.Injective π_hom
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro P hP; rw [RingHom.mem_ker] at hP; rw [Submodule.mem_bot]
  by_contra hP_ne
  obtain ⟨s, hs_mem, hs_min⟩ := Finset.exists_min_image P.support
    (fun d : GenIdx →₀ ℕ => d.sum (fun i c => if i.2 = (1 : Fin 2) then c else 0))
    (MvPolynomial.support_nonempty.mpr hP_ne)
  have hs_coeff : P.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs_mem
  set D_s := T_diag (∏ p ∈ primesOf s, ppowDiag 2 p.1
    ![toPrimeExp s p 1, toPrimeExp s p 0 + toPrimeExp s p 1])
  have h_zero : (π_hom P) D_s = 0 := by rw [hP]; rfl
  change (MvPolynomial.eval₂ (Int.castRingHom (HeckeAlgebra 2))
    (fun i : GenIdx => T_gen 2 i.1.1 i.2) P) D_s = 0 at h_zero
  rw [MvPolynomial.eval₂_eq, Finset.sum_apply'] at h_zero
  have h_term : ∀ d ∈ P.support,
      (((Int.castRingHom (HeckeAlgebra 2)) (P.coeff d)) *
        (∏ i ∈ d.support, T_gen 2 i.1.1 i.2 ^ d i)) D_s =
      P.coeff d * (∏ i ∈ d.support, T_gen 2 i.1.1 i.2 ^ d i) D_s := by
    intro d _
    show (((P.coeff d : ℤ) : HeckeAlgebra 2) *
      (∏ i ∈ d.support, T_gen 2 i.1.1 i.2 ^ d i)) D_s = _
    rw [show ((P.coeff d : ℤ) : HeckeAlgebra 2) =
      (P.coeff d) • (1 : HeckeAlgebra 2) from (zsmul_one _).symm,
      smul_mul_assoc, one_mul, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl h_term] at h_zero
  conv at h_zero =>
    arg 1; arg 2; ext d
    rw [show (∏ i ∈ d.support, T_gen 2 i.1.1 i.2 ^ d i) =
      ∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
        T_gen 2 p.1 1 ^ (toPrimeExp d p 1)) from monomial_eval_eq_prod_primes d]
  have h_delta : ∀ d ∈ P.support,
      P.coeff d * (∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
        T_gen 2 p.1 1 ^ (toPrimeExp d p 1))) D_s =
      if d = s then P.coeff d else 0 := by
    intro d hd_mem
    by_cases hds : d = s
    · rw [hds]; simp only [ite_true]
      rw [multi_prime_coeff_factor (primesOf s) (toPrimeExp s) (toPrimeExp s)]
      simp only [Finset.prod_congr rfl (fun p _ =>
        HeckeRing.GLn.Inj.monomial_eval_kronecker p.1 p.2
          (toPrimeExp s p 0) (toPrimeExp s p 1)
          (toPrimeExp s p 0) (toPrimeExp s p 1) le_rfl)]
      simp [mul_one]
    · simp only [hds, ite_false]
      suffices (∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
        T_gen 2 p.1 1 ^ (toPrimeExp d p 1))) D_s = 0 by rw [this, mul_zero]
      by_cases h_det_eq :
          ∏ p ∈ primesOf d, p.1 ^ (toPrimeExp d p 0 + 2 * toPrimeExp d p 1) =
          ∏ p ∈ primesOf s, p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1)
      · -- Same det ⟹ same prime set
        have h_same_primes : primesOf d = primesOf s := by
          -- Equal products of prime powers ⟹ same prime set
          -- For each p ∈ primesOf d: p | ∏_{primesOf d} = ∏_{primesOf s}, so p ∈ primesOf s.
          have h_exp_pos : ∀ (e : GenIdx →₀ ℕ) (p : {p : ℕ // p.Prime}), p ∈ primesOf e →
              0 < toPrimeExp e p 0 + 2 * toPrimeExp e p 1 := by
            intro e p hp
            obtain ⟨⟨q, k⟩, hq_mem, hq_eq⟩ := Finset.mem_image.mp hp
            simp only at hq_eq
            subst hq_eq
            have hq_ne_zero : e (q, k) ≠ 0 := Finsupp.mem_support_iff.mp hq_mem
            fin_cases k <;> simp [toPrimeExp] at hq_ne_zero ⊢ <;> omega
          ext p
          constructor
          · intro hp
            have h_term_dvd : p.1 ^ (toPrimeExp d p 0 + 2 * toPrimeExp d p 1) ∈
                (primesOf d).image (fun q => q.1 ^ (toPrimeExp d q 0 + 2 * toPrimeExp d q 1)) :=
              Finset.mem_image.mpr ⟨p, hp, rfl⟩
            have h_p_dvd_term : p.1 ∣ p.1 ^ (toPrimeExp d p 0 + 2 * toPrimeExp d p 1) :=
              dvd_pow_self _ (Nat.pos_iff_ne_zero.mp (h_exp_pos d p hp))
            have h_term_dvd_prod :
                p.1 ^ (toPrimeExp d p 0 + 2 * toPrimeExp d p 1) ∣
                ∏ q ∈ primesOf d, q.1 ^ (toPrimeExp d q 0 + 2 * toPrimeExp d q 1) :=
              Finset.dvd_prod_of_mem _ hp
            have hdvd_full : p.1 ∣
                ∏ q ∈ primesOf s, q.1 ^ (toPrimeExp s q 0 + 2 * toPrimeExp s q 1) :=
              h_det_eq ▸ (h_p_dvd_term.trans h_term_dvd_prod)
            rw [p.2.prime.dvd_finset_prod_iff] at hdvd_full
            obtain ⟨q, hq, hpq⟩ := hdvd_full
            have h_eq : p.1 = q.1 :=
              (Nat.prime_dvd_prime_iff_eq p.2 q.2).mp (p.2.dvd_of_dvd_pow hpq)
            rw [show p = q from Subtype.ext h_eq]; exact hq
          · intro hp
            have h_p_dvd_term : p.1 ∣ p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1) :=
              dvd_pow_self _ (Nat.pos_iff_ne_zero.mp (h_exp_pos s p hp))
            have h_term_dvd_prod :
                p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1) ∣
                ∏ q ∈ primesOf s, q.1 ^ (toPrimeExp s q 0 + 2 * toPrimeExp s q 1) :=
              Finset.dvd_prod_of_mem _ hp
            have hdvd_full : p.1 ∣
                ∏ q ∈ primesOf d, q.1 ^ (toPrimeExp d q 0 + 2 * toPrimeExp d q 1) :=
              h_det_eq ▸ (h_p_dvd_term.trans h_term_dvd_prod)
            rw [p.2.prime.dvd_finset_prod_iff] at hdvd_full
            obtain ⟨q, hq, hpq⟩ := hdvd_full
            have h_eq : p.1 = q.1 :=
              (Nat.prime_dvd_prime_iff_eq p.2 q.2).mp (p.2.dvd_of_dvd_pow hpq)
            rw [show p = q from Subtype.ext h_eq]; exact hq
        rw [h_same_primes,
          multi_prime_coeff_factor (primesOf s) (toPrimeExp d) (toPrimeExp s)]
        have ⟨p₀, hp₀_mem, hp₀_lt⟩ : ∃ p₀ ∈ primesOf s,
            toPrimeExp s p₀ 1 < toPrimeExp d p₀ 1 := by
          by_contra h_all_le; push_neg at h_all_le
          apply hds; ext ⟨p, k⟩
          by_cases hp : p ∈ primesOf s
          · have h_per_prime : toPrimeExp d p 0 + 2 * toPrimeExp d p 1 =
                toPrimeExp s p 0 + 2 * toPrimeExp s p 1 := by
              have h_fact := congr_arg (fun n => n.factorization p.1) (h_same_primes ▸ h_det_eq)
              dsimp only at h_fact
              rw [Nat.factorization_prod_apply
                (fun (q : {p : ℕ // p.Prime}) _ => pow_ne_zero _ q.2.ne_zero),
                  Nat.factorization_prod_apply
                (fun (q : {p : ℕ // p.Prime}) _ => pow_ne_zero _ q.2.ne_zero)] at h_fact
              have h_each : ∀ (x : {p : ℕ // p.Prime}) (e : ℕ),
                  (x.1 ^ e).factorization p.1 = if x = p then e else 0 := by
                intro x e
                rw [Nat.Prime.factorization_pow x.2, Finsupp.single_apply]
                by_cases hxp : x = p
                · rw [if_pos hxp, if_pos (congr_arg Subtype.val hxp)]
                · rw [if_neg hxp, if_neg (fun h => hxp (Subtype.ext h))]
              conv at h_fact =>
                lhs; arg 2; ext x; rw [h_each x _]
              conv at h_fact =>
                rhs; arg 2; ext x; rw [h_each x _]
              rw [Finset.sum_ite_eq_of_mem' _ p _ hp,
                  Finset.sum_ite_eq_of_mem' _ p _ hp] at h_fact
              exact h_fact
            have h_le := h_all_le p hp
            set T := d.support ∪ s.support
            set g := fun (i : GenIdx) (c : ℕ) => if i.2 = (1 : Fin 2) then c else 0
            have hd_sum : d.sum g = ∑ i ∈ T, g i (d i) := by
              show ∑ i ∈ d.support, g i (d i) = ∑ i ∈ T, g i (d i)
              exact Finset.sum_subset Finset.subset_union_left
                (fun i _ hi => by simp [g, Finsupp.notMem_support_iff.mp hi])
            have hs_sum : s.sum g = ∑ i ∈ T, g i (s i) := by
              show ∑ i ∈ s.support, g i (s i) = ∑ i ∈ T, g i (s i)
              exact Finset.sum_subset Finset.subset_union_right
                (fun i _ hi => by simp [g, Finsupp.notMem_support_iff.mp hi])
            have h_ptwise : ∀ i ∈ T, g i (d i) ≤ g i (s i) := by
              intro ⟨q, k'⟩ _; simp only [g]
              split_ifs with hk
              · by_cases hq : q ∈ primesOf s
                · have := h_all_le q hq
                  show d (q, k') ≤ s (q, k')
                  rw [hk]; exact this
                · have hq_d : (q, k') ∉ d.support := fun h =>
                    (h_same_primes ▸ hq) (Finset.mem_image.mpr ⟨_, h, rfl⟩)
                  rw [Finsupp.notMem_support_iff.mp hq_d]; exact Nat.zero_le _
              · exact le_refl 0
            have h_dg_le : d.sum g ≤ s.sum g := by
              rw [hd_sum, hs_sum]; exact Finset.sum_le_sum h_ptwise
            have h_sum_eq : d.sum g = s.sum g := le_antisymm h_dg_le
              (hs_min d (MvPolynomial.mem_support_iff.mpr
                (MvPolynomial.mem_support_iff.mp hd_mem)))
            have h_eq1 : toPrimeExp d p 1 = toPrimeExp s p 1 := by
              by_contra h_ne
              have hlt : g (p, (1 : Fin 2)) (d (p, 1)) < g (p, (1 : Fin 2)) (s (p, 1)) := by
                simp only [g]; exact lt_of_le_of_ne h_le h_ne
              have h_sum_strict : ∑ i ∈ T, g i (d i) < ∑ i ∈ T, g i (s i) :=
                Finset.sum_lt_sum h_ptwise ⟨(p, 1), Finset.mem_union.mpr
                  (Or.inr (Finsupp.mem_support_iff.mpr (by
                    intro h
                    have hlt' : g (p, (1 : Fin 2)) (d (p, 1)) < g (p, (1 : Fin 2)) 0 := h ▸ hlt
                    simp [g] at hlt'))), hlt⟩
              linarith [hd_sum ▸ hs_sum ▸ h_sum_eq]
            fin_cases k
            · show d (p, 0) = s (p, 0)
              show toPrimeExp d p 0 = toPrimeExp s p 0
              omega
            · show d (p, 1) = s (p, 1)
              exact h_eq1
          · have hp' : p ∉ primesOf d := h_same_primes ▸ hp
            simp only [toPrimeExp] at *
            have : (p, k) ∉ d.support := fun h => hp' (Finset.mem_image.mpr ⟨_, h, rfl⟩)
            have : (p, k) ∉ s.support := fun h => hp (Finset.mem_image.mpr ⟨_, h, rfl⟩)
            simp [Finsupp.notMem_support_iff.mp ‹(p,k) ∉ d.support›,
                  Finsupp.notMem_support_iff.mp ‹(p,k) ∉ s.support›]
        apply Finset.prod_eq_zero hp₀_mem
        rw [HeckeRing.GLn.Inj.monomial_eval_kronecker p₀.1 p₀.2
          (toPrimeExp d p₀ 0) (toPrimeExp d p₀ 1)
          (toPrimeExp s p₀ 0) (toPrimeExp s p₀ 1) hp₀_lt.le]
        simp only [ite_eq_right_iff, one_ne_zero]
        intro ⟨_, h1⟩; exact absurd h1 (Nat.ne_of_gt hp₀_lt)
      · exact monomial_eval_zero_of_det_ne d s h_det_eq
  rw [Finset.sum_congr rfl h_delta] at h_zero
  rw [Finset.sum_ite_eq_of_mem' (P.support) s _ hs_mem] at h_zero
  exact hs_coeff h_zero

/-- `π_hom` is injective: the Hecke algebra generators are algebraically independent,
so the free polynomial ring `ℤ[X_{(p,k)}]` embeds faithfully into `HeckeAlgebra 2`. -/
private lemma π_injective : Function.Injective π_hom := by
  have h := algebraicIndependent_iff_injective_aeval.mp T_gen_algebraicIndependent
  intro a b hab; exact h hab

/-- **Kernel compatibility**: `ker π ≤ ker ψ`.
Since `π_hom` is injective, `ker π_hom = ⊥ ≤ ker (ψ_hom N)`. -/
private lemma ker_π_le_ker_ψ :
    RingHom.ker π_hom ≤ RingHom.ker (ψ_hom N) := by
  rw [(RingHom.injective_iff_ker_eq_bot π_hom).mp π_injective]
  exact bot_le

set_option maxHeartbeats 800000 in
/-- The product element in a scalar × diagonal mulMap lands in the GL DC of the product diagonal.
Uses scalar centrality: `diag(c,c) * g = g * diag(c,c)` for all `g`. -/
private lemma product_mem_GL_DC_scalar
    (c : ℕ) (hc : 0 < c) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (hc_gcd : Int.gcd (↑c) ↑N = 1) (ha_gcd : Int.gcd (a 0) N = 1)
    (p : HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N
          (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd)) ×
      HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd))) :
    (p.1.out : GL (Fin 2) ℚ) * HeckeCoset.rep (T_diag_Gamma0 N
        (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd) *
      ((p.2.out : GL (Fin 2) ℚ) * HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd)) ∈
    DoubleCoset.doubleCoset (diagMat 2 ((fun _ : Fin 2 => c) * a) : GL (Fin 2) ℚ)
      (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _) := by
  have hc_rep := HeckeCoset.rep_mem (T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd)
  simp only [T_diag_Gamma0, HeckeCoset.toSet_mk] at hc_rep
  have ha_rep := HeckeCoset.rep_mem (T_diag_Gamma0 N a ha ha_gcd)
  simp only [T_diag_Gamma0, HeckeCoset.toSet_mk] at ha_rep
  have hc_gl := Gamma0_doubleCoset_subset_Gamma N _ hc_rep
  have ha_gl := Gamma0_doubleCoset_subset_Gamma N _ ha_rep
  rw [DoubleCoset.mem_doubleCoset] at hc_gl ha_gl
  obtain ⟨L_c, ⟨σL_c, rfl⟩, R_c, ⟨σR_c, rfl⟩, hc_eq⟩ := hc_gl
  obtain ⟨L_a, ⟨σL_a, rfl⟩, R_a, ⟨σR_a, rfl⟩, ha_eq⟩ := ha_gl
  obtain ⟨σp₁, hp₁_eq⟩ := Gamma0_le_SLnZ N (SetLike.coe_mem p.1.out)
  obtain ⟨σp₂, hp₂_eq⟩ := Gamma0_le_SLnZ N (SetLike.coe_mem p.2.out)
  set X : GL (Fin 2) ℚ := mapGL ℚ (σp₁ * σL_c * σR_c * σp₂ * σL_a) *
    diagMat 2 ((fun _ : Fin 2 => c) * a) * mapGL ℚ σR_a with hX_def
  have h_rewrite : (p.1.out : GL (Fin 2) ℚ) *
      HeckeCoset.rep (T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd) *
      ((p.2.out : GL (Fin 2) ℚ) * HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd)) = X := by
    simp only [T_diag_Gamma0]
    rw [← hp₁_eq, ← hp₂_eq, hc_eq, ha_eq]
    show mapGL ℚ σp₁ * (mapGL ℚ σL_c * diagMat 2 (fun _ => c) * mapGL ℚ σR_c) *
      (mapGL ℚ σp₂ * (mapGL ℚ σL_a * diagMat 2 a * mapGL ℚ σR_a)) = X
    rw [hX_def]
    calc mapGL ℚ σp₁ * (mapGL ℚ σL_c * diagMat 2 (fun _ => c) * mapGL ℚ σR_c) *
          (mapGL ℚ σp₂ * (mapGL ℚ σL_a * diagMat 2 a * mapGL ℚ σR_a))
        = mapGL ℚ σp₁ * mapGL ℚ σL_c *
          (diagMat 2 (fun _ => c) * (mapGL ℚ σR_c * mapGL ℚ σp₂ * mapGL ℚ σL_a)) *
          (diagMat 2 a * mapGL ℚ σR_a) := by group
      _ = mapGL ℚ σp₁ * mapGL ℚ σL_c *
          ((mapGL ℚ σR_c * mapGL ℚ σp₂ * mapGL ℚ σL_a) * diagMat 2 (fun _ => c)) *
          (diagMat 2 a * mapGL ℚ σR_a) := by rw [diagMat_scalar_comm 2 c hc]
      _ = mapGL ℚ (σp₁ * σL_c * σR_c * σp₂ * σL_a) *
          (diagMat 2 (fun _ => c) * diagMat 2 a) * mapGL ℚ σR_a := by
            simp only [map_mul]; group
      _ = mapGL ℚ (σp₁ * σL_c * σR_c * σp₂ * σL_a) *
          diagMat 2 ((fun _ => c) * a) * mapGL ℚ σR_a := by
            rw [diagMat_mul 2 _ a (fun _ => hc) ha]
  rw [h_rewrite]
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨mapGL ℚ (σp₁ * σL_c * σR_c * σp₂ * σL_a),
    ⟨σp₁ * σL_c * σR_c * σp₂ * σL_a, rfl⟩,
    mapGL ℚ σR_a, ⟨σR_a, rfl⟩, hX_def⟩

/-- Every mulMap output for scalar × arbitrary in the Gamma0 Hecke algebra
equals `T_diag_Gamma0 N ((fun _ => c) * a)`. -/
private lemma mulMap_Gamma0_scalar_eq
    (c : ℕ) (hc : 0 < c) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (hc_gcd : Int.gcd (↑c) ↑N = 1) (ha_gcd : Int.gcd (a 0) N = 1)
    (hdiv : a 0 ∣ a 1)
    (hca_gcd : Int.gcd ((((fun _ : Fin 2 => c) * a) 0 : ℕ) : ℤ) ↑N = 1)
    (p : HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N
          (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd)) ×
      HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd))) :
    HeckeRing.mulMap (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd))
      (HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd)) p =
    T_diag_Gamma0 N ((fun _ : Fin 2 => c) * a)
      (fun i => Nat.mul_pos hc (ha i)) hca_gcd := by
  set D := HeckeRing.mulMap (Gamma0_pair N) _ _ p
  obtain ⟨b, hb, hgcd_b, hdiv_b, hrep⟩ := Gamma0_exists_diag_rep N (HeckeCoset.rep D)
  have hrep' : D = T_diag_Gamma0 N b hb hgcd_b := by rw [← hrep]; exact (HeckeCoset.mk_rep D).symm
  have hGL : cosetMap N D = T_diag b := by rw [hrep', cosetMap_T_diag_Gamma0]
  have hGL_ca : cosetMap N D = T_diag ((fun _ : Fin 2 => c) * a) := by
    apply cosetMap_mulMap_mem_GL_DC N _ _ p _
    have h_mem := product_mem_GL_DC_scalar N c hc a ha hc_gcd ha_gcd p
    have h_pos : ∀ i : Fin 2, 0 < ((fun _ : Fin 2 => c) * a) i :=
      fun i => Nat.mul_pos hc (ha i)
    have h_eq : DoubleCoset.doubleCoset
        (diagMat 2 ((fun _ : Fin 2 => c) * a) : GL (Fin 2) ℚ)
        ((SLnZ_subgroup 2) : Set _) ((SLnZ_subgroup 2) : Set _) =
        DoubleCoset.doubleCoset
        (↑(T_diag ((fun _ : Fin 2 => c) * a)).rep : GL (Fin 2) ℚ)
        ((GL_pair 2).H : Set _) ((GL_pair 2).H : Set _) := by
      rw [show (diagMat 2 ((fun _ : Fin 2 => c) * a) : GL (Fin 2) ℚ) =
          ↑(diagMat_delta 2 ((fun _ : Fin 2 => c) * a)) from
          (diagMat_delta_val 2 _ h_pos).symm]
      have h_toSet := HeckeCoset.toSet_eq_rep (T_diag ((fun _ : Fin 2 => c) * a))
      simp only [HeckeCoset.toSet, T_diag] at h_toSet
      exact h_toSet
    rw [← h_eq]
    exact h_mem
  have hdiv_b' : DivChain 2 b := fun i hi => (show i = 0 by omega) ▸ hdiv_b
  have hdiv_ca : DivChain 2 ((fun _ : Fin 2 => c) * a) := fun i hi => by
    have h0 : (⟨i, by omega⟩ : Fin 2) = (0 : Fin 2) := Fin.ext (show i = 0 by omega)
    have h1 : (⟨i + 1, hi⟩ : Fin 2) = (1 : Fin 2) := Fin.ext (show i + 1 = 1 by omega)
    show ((fun _ : Fin 2 => c) * a) ⟨i, _⟩ ∣ ((fun _ : Fin 2 => c) * a) ⟨i + 1, hi⟩
    rw [h0, h1]; simp only [Pi.mul_apply]; exact Nat.mul_dvd_mul_left c hdiv
  have hb_eq : b = (fun _ : Fin 2 => c) * a := diagonal_representative_unique 2 b
    ((fun _ : Fin 2 => c) * a) hb (fun i => Nat.mul_pos hc (ha i)) hdiv_b' hdiv_ca
    (by rw [← hGL, hGL_ca])
  subst hb_eq; exact hrep'

/-- The degree of a scalar Gamma0 double coset `T'(c, c)` is `1`:
`diag(c,c)` centralizes all of `GL₂(ℚ)`, hence the stabilizer is all of `Γ₀(N)`. -/
private lemma Gamma0_HeckeCoset_deg_scalar (c : ℕ) (hc : 0 < c)
    (hc_gcd : Int.gcd (↑c) ↑N = 1) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd) = 1 := by
  set D := T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd
  set δ := HeckeCoset.rep D
  set H := (Gamma0_pair N).H
  suffices hsmul : ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H = H by
    have h_def : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D =
        ↑((ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H).relIndex H) := by
      simp only [HeckeRing.HeckeCoset_deg, Subgroup.relIndex, Subgroup.index,
        ← Nat.card_eq_fintype_card]; rfl
    rw [h_def, hsmul, Subgroup.relIndex_self]; simp
  have hδ_mem : (δ : GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ) H H := by
    have h1 : HeckeCoset.toSet D =
        DoubleCoset.doubleCoset (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ) H H := by
      simp only [D, T_diag_Gamma0, HeckeCoset.toSet_mk]; rfl
    rw [← h1]; exact HeckeCoset.rep_mem D
  rw [DoubleCoset.mem_doubleCoset] at hδ_mem; obtain ⟨h₁, hh₁, h₂, hh₂, hδ_eq⟩ := hδ_mem
  have hδ_simp : (δ : GL (Fin 2) ℚ) = (h₁ * h₂) * diagMat 2 (fun _ : Fin 2 => c) := by
    rw [hδ_eq, mul_assoc, diagMat_scalar_comm 2 c hc h₂, ← mul_assoc]
  rw [hδ_simp, map_mul, ← smul_smul]
  have hscalar_smul : ConjAct.toConjAct (diagMat 2 (fun _ : Fin 2 => c)) • H = H := by
    ext x; constructor
    · intro hx; rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
      simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hx
      rwa [diagMat_scalar_conj_eq 2 c hc] at hx
    · intro hx; rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
      rwa [diagMat_scalar_conj_eq 2 c hc]
  rw [hscalar_smul]
  ext x; simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  constructor
  · intro hx; have : x = (h₁ * h₂) * ((h₁ * h₂)⁻¹ * x * (h₁ * h₂)) * (h₁ * h₂)⁻¹ := by group
    rw [this]; exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) hx) (H.inv_mem (H.mul_mem hh₁ hh₂))
  · intro hx; exact H.mul_mem (H.mul_mem (H.inv_mem (H.mul_mem hh₁ hh₂)) hx) (H.mul_mem hh₁ hh₂)

/-- **Generalized Gamma0-level scalar multiplication**: `T'(c,c) * T'(a₀,a₁) = T'(c*a₀, c*a₁)`.
The scalar `diag(c,c)` centralizes `Γ₀(N)`, so its double coset has degree 1
and the unique mulMap output is `T'(c*a₀, c*a₁)` with multiplicity 1. -/
private lemma T_Gamma0_scalar_mul_gen (c : ℕ) (hc : 0 < c) (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hc_gcd : Int.gcd (↑c) ↑N = 1)
    (ha_gcd : Int.gcd (a 0) N = 1) (hdiv : a 0 ∣ a 1) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd) 1 *
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N a ha ha_gcd) 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N ((fun _ : Fin 2 => c) * a)
        (fun i => Nat.mul_pos hc (ha i))
        (by show Int.gcd (↑(c * a 0)) ↑N = 1
            simp only [Int.gcd_natCast_natCast]
            exact Nat.Coprime.mul_left
              (by rwa [Int.gcd_natCast_natCast] at hc_gcd)
              (by rwa [Int.gcd_natCast_natCast] at ha_gcd))) 1 := by
  set D_c := T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd
  set D_a := T_diag_Gamma0 N a ha ha_gcd
  have hca_gcd' : Int.gcd ((((fun _ : Fin 2 => c) * a) 0 : ℕ) : ℤ) ↑N = 1 := by
    show Int.gcd ((c * a 0 : ℕ) : ℤ) ↑N = 1
    simp only [Int.gcd_natCast_natCast]
    exact Nat.Coprime.mul_left
      (by rwa [Int.gcd_natCast_natCast] at hc_gcd)
      (by rwa [Int.gcd_natCast_natCast] at ha_gcd)
  set D_out := T_diag_Gamma0 N ((fun _ : Fin 2 => c) * a)
    (fun i => Nat.mul_pos hc (ha i)) hca_gcd'
  change HeckeRing.T_single _ ℤ D_c 1 * HeckeRing.T_single _ ℤ D_a 1 =
    HeckeRing.T_single _ ℤ D_out 1
  have h_mulMap : ∀ p, HeckeRing.mulMap (Gamma0_pair N) D_c.rep D_a.rep p = D_out :=
    mulMap_Gamma0_scalar_eq N c hc a ha hc_gcd ha_gcd hdiv hca_gcd'
  refine HeckeRing.T_single_one_mul_eq_single (Gamma0_pair N) D_c D_a D_out ?_ ?_
  · have h_card : Fintype.card (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) = 1 := by
      have := Gamma0_HeckeCoset_deg_scalar N c hc hc_gcd
      simp only [HeckeRing.HeckeCoset_deg] at this; exact_mod_cast this
    haveI : Subsingleton (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_card)
    have h_le : HeckeRing.heckeMultiplicity (Gamma0_pair N) D_c.rep D_a.rep D_out.rep ≤ 1 := by
      classical
      simp only [HeckeRing.heckeMultiplicity]; norm_cast; rw [Nat.card_eq_fintype_card]
      apply Fintype.card_le_one_iff_subsingleton.mpr; constructor
      intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
      have hi : i₁ = i₂ := Subsingleton.elim i₁ i₂; subst hi
      simp only [Set.mem_setOf_eq] at h₁ h₂
      have hj := HeckeRing.decompQuot_snd_eq_of_fst_eq (Gamma0_pair N) D_c.rep D_a.rep D_out.rep i₁ j₁ j₂ h₁ h₂
      subst hj; rfl
    have h_pos : 0 < HeckeRing.heckeMultiplicity (Gamma0_pair N) D_c.rep D_a.rep D_out.rep := by
      have h_mem : D_out ∈ HeckeRing.mulSupport (Gamma0_pair N) D_c.rep D_a.rep := by
        simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
          true_and, Prod.exists]
        have ⟨i₀⟩ : Nonempty (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) :=
          Fintype.card_pos_iff.mp (h_card ▸ Nat.one_pos)
        have ⟨j₀⟩ : Nonempty (HeckeRing.decompQuot (Gamma0_pair N) D_a.rep) :=
          Fintype.card_pos_iff.mp (by
            have := HeckeRing.HeckeCoset_deg_pos (Gamma0_pair N) D_a
            simp only [HeckeRing.HeckeCoset_deg] at this; omega)
        exact ⟨i₀, j₀, h_mulMap (i₀, j₀)⟩
      exact HeckeRing.heckeMultiplicity_pos_of_mem (Gamma0_pair N) _ _ _ h_mem
    omega
  · intro A hA
    exact HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique (Gamma0_pair N) _ _ D_out A hA h_mulMap

/-- **Gamma0-level scalar multiplication**: `T'(c,c) * T'(1,m) = T'(c, c*m)`.
The scalar `diag(c,c)` centralizes `Γ₀(N)`, so its double coset has degree 1
and the unique mulMap output is `T'(c, c*m)` with multiplicity 1.
This is used for the `d₁ > 1` case of surjectivity (Shimura Thm 3.34). -/
private lemma T_Gamma0_scalar_mul (c m : ℕ) (hc : 0 < c) (hm : 0 < m)
    (hc_gcd : Int.gcd (↑c) ↑N = 1) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd) 1 *
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m]) (fun i => by fin_cases i <;> simp [hm]) (by simp)) 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N ((fun _ : Fin 2 => c) * ![1, m])
        (fun i => Nat.mul_pos hc (by fin_cases i <;> simp [hm]))
        (by show Int.gcd (↑(c * 1)) ↑N = 1; simp [hc_gcd])) 1 := by
  set D_c := T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd
  set D_m := T_diag_Gamma0 N (![1, m]) (fun i => by fin_cases i <;> simp [hm]) (by simp)
  set D_out := T_diag_Gamma0 N ((fun _ : Fin 2 => c) * ![1, m])
    (fun i => Nat.mul_pos hc (by fin_cases i <;> simp [hm]))
    (by show Int.gcd (↑(c * 1)) ↑N = 1; simp [hc_gcd])
  change HeckeRing.T_single _ ℤ D_c 1 * HeckeRing.T_single _ ℤ D_m 1 =
    HeckeRing.T_single _ ℤ D_out 1
  have hca_gcd : Int.gcd ((((fun _ : Fin 2 => c) * (![1, m] : Fin 2 → ℕ)) 0 : ℕ) : ℤ) ↑N = 1 := by
    simp [hc_gcd]
  have h_mulMap : ∀ p, HeckeRing.mulMap (Gamma0_pair N) D_c.rep D_m.rep p = D_out := by
    intro p
    have h := mulMap_Gamma0_scalar_eq N c hc ![1, m]
      (fun i => by fin_cases i <;> simp [hm]) hc_gcd (by simp) (by simp) hca_gcd p
    convert h using 2
  refine HeckeRing.T_single_one_mul_eq_single (Gamma0_pair N) D_c D_m D_out ?_ ?_
  · have h_card : Fintype.card (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) = 1 := by
      have := Gamma0_HeckeCoset_deg_scalar N c hc hc_gcd
      simp only [HeckeRing.HeckeCoset_deg] at this; exact_mod_cast this
    haveI : Subsingleton (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_card)
    have h_le : HeckeRing.heckeMultiplicity (Gamma0_pair N) D_c.rep D_m.rep D_out.rep ≤ 1 := by
      classical
      simp only [HeckeRing.heckeMultiplicity]; norm_cast; rw [Nat.card_eq_fintype_card]
      apply Fintype.card_le_one_iff_subsingleton.mpr; constructor
      intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
      have hi : i₁ = i₂ := Subsingleton.elim i₁ i₂; subst hi
      simp only [Set.mem_setOf_eq] at h₁ h₂
      have hj := HeckeRing.decompQuot_snd_eq_of_fst_eq (Gamma0_pair N) D_c.rep D_m.rep D_out.rep i₁ j₁ j₂ h₁ h₂
      subst hj; rfl
    have h_pos : 0 < HeckeRing.heckeMultiplicity (Gamma0_pair N) D_c.rep D_m.rep D_out.rep := by
      have h_mem : D_out ∈ HeckeRing.mulSupport (Gamma0_pair N) D_c.rep D_m.rep := by
        simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
          true_and, Prod.exists]
        have ⟨i₀⟩ : Nonempty (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) :=
          Fintype.card_pos_iff.mp (h_card ▸ Nat.one_pos)
        have ⟨j₀⟩ : Nonempty (HeckeRing.decompQuot (Gamma0_pair N) D_m.rep) :=
          Fintype.card_pos_iff.mp (by
            have := HeckeRing.HeckeCoset_deg_pos (Gamma0_pair N) D_m
            simp only [HeckeRing.HeckeCoset_deg] at this; omega)
        exact ⟨i₀, j₀, h_mulMap (i₀, j₀)⟩
      exact HeckeRing.heckeMultiplicity_pos_of_mem (Gamma0_pair N) _ _ _ h_mem
    omega
  · intro A hA
    exact HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique (Gamma0_pair N) _ _ D_out A hA h_mulMap

/-- **T'(1,p) ∈ range(ψ)** for any prime p: follows directly from ψ_hom definition. -/
private lemma T_1p_mem_ψ_range (p : ℕ) (hp : p.Prime) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p])
        (fun i => by fin_cases i <;> simp [hp.pos])
        (by simp)) 1 ∈ (ψ_hom N).range :=
  ⟨MvPolynomial.X (⟨p, hp⟩, (0 : Fin 2)), by
    show ψ_hom N (MvPolynomial.X (⟨p, hp⟩, (0 : Fin 2))) = _
    simp only [ψ_hom, MvPolynomial.eval₂Hom_X']; rfl⟩

/-- **T'(p,p) ∈ range(ψ)** for prime p with p ∤ N: follows from ψ_hom definition
since `X_{(p,1)} ↦ T'(p,p)` when p ∤ N. -/
private lemma T_pp_mem_ψ_range (p : ℕ) (hp : p.Prime) (hpN : (p : ℤ).gcd N = 1) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![p, p])
        (fun i => by fin_cases i <;> simp [hp.pos])
        (by show Int.gcd (↑p) ↑N = 1; exact hpN)) 1 ∈ (ψ_hom N).range := by
  have hp_not_dvd_N : ¬(p ∣ N) := by
    intro h; rw [Int.gcd_natCast_natCast] at hpN
    exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, dvd_refl p, h⟩ hpN
  refine ⟨MvPolynomial.X (⟨p, hp⟩, (1 : Fin 2)), ?_⟩
  show ψ_hom N (MvPolynomial.X (⟨p, hp⟩, (1 : Fin 2))) = _
  simp only [ψ_hom, MvPolynomial.eval₂Hom_X']
  simp only [show (1 : Fin 2) ≠ 0 from by omega, ↓reduceIte, dif_neg hp_not_dvd_N]

/-- **T'(p, p^j) ∈ range(ψ)** for prime p with p ∤ N, j ≥ 1, given that
    T'(1, p^(j-1)) ∈ range. Uses T_Gamma0_scalar_mul to factor T'(p, p) * T'(1, p^(j-1)). -/
private lemma T_p_ppow_mem_ψ_range (p : ℕ) (hp : p.Prime) (hpN : (p : ℤ).gcd N = 1)
    (j : ℕ) (hj : 1 ≤ j)
    (h_IH : HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p^(j-1)])
        (fun i => by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) 1 ∈ (ψ_hom N).range) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![p, p^j])
        (fun i => by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
        (by show Int.gcd (↑p) ↑N = 1; exact hpN)) 1 ∈ (ψ_hom N).range := by
  have h_Tpp := T_pp_mem_ψ_range N p hp hpN
  have h_pp_eq : T_diag_Gamma0 N (![p, p])
      (fun i => by fin_cases i <;> simp [hp.pos])
      (by show Int.gcd (↑p) ↑N = 1; exact hpN) =
    T_diag_Gamma0 N (fun _ : Fin 2 => p) (fun _ => hp.pos) hpN := by
    congr 1
    funext i; fin_cases i <;> rfl
  rw [h_pp_eq] at h_Tpp
  have h_mul := T_Gamma0_scalar_mul N p (p^(j-1)) hp.pos (pow_pos hp.pos _) hpN
  have h_diag_eq : (fun _ : Fin 2 => p) * ![1, p^(j-1)] = ![p, p^j] := by
    funext i
    fin_cases i
    · show p * 1 = p; ring
    · show p * p^(j-1) = p^j
      rw [← pow_succ', show j - 1 + 1 = j from Nat.sub_add_cancel hj]
  have h_eq : T_diag_Gamma0 N ((fun _ : Fin 2 => p) * ![1, p^(j-1)])
      (fun i => Nat.mul_pos hp.pos (by fin_cases i <;> simp [pow_pos hp.pos]))
      (by show Int.gcd (↑(p * 1)) ↑N = 1; simp [hpN]) =
    T_diag_Gamma0 N (![p, p^j])
      (fun i => by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
      (by show Int.gcd (↑p) ↑N = 1; exact hpN) := by
    show (⟦⟨diagMat 2 ((fun _ : Fin 2 => p) * ![1, p^(j-1)]), _⟩⟧ : HeckeCoset _) =
         ⟦⟨diagMat 2 ![p, p^j], _⟩⟧
    congr 1
    apply Subtype.ext
    show diagMat 2 ((fun _ : Fin 2 => p) * ![1, p^(j-1)]) = diagMat 2 ![p, p^j]
    rw [h_diag_eq]
  rw [h_eq] at h_mul
  rw [← h_mul]
  exact (ψ_hom N).range.mul_mem h_Tpp h_IH

/-- **Helper**: extract a Γ₀(N)-level decomposition of `rep(T_diag_Gamma0 N a)` in
    `DC_{Γ₀(N)}(diagMat 2 a)`. -/
private lemma Gamma0_T_diag_rep_decompose (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1) :
    ∃ L ∈ (Gamma0_pair N).H, ∃ R ∈ (Gamma0_pair N).H,
      (HeckeCoset.rep (T_diag_Gamma0 N a ha hgcd) : GL (Fin 2) ℚ) =
        L * diagMat 2 a * R := by
  have h_rep := HeckeCoset.rep_mem (T_diag_Gamma0 N a ha hgcd)
  simp only [T_diag_Gamma0, HeckeCoset.toSet_mk] at h_rep
  rw [DoubleCoset.mem_doubleCoset] at h_rep
  obtain ⟨L, hL, R, hR, hLR_eq⟩ := h_rep
  exact ⟨L, hL, R, hR, hLR_eq⟩

/-- Determinant of `rep(T_diag_Gamma0 N a)` equals the product of entries of `a`. -/
private lemma Gamma0_T_diag_rep_det (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (hgcd : Int.gcd (a 0) N = 1) :
    (HeckeCoset.rep (T_diag_Gamma0 N a ha hgcd) : GL (Fin 2) ℚ).val.det =
      ((a 0 * a 1 : ℕ) : ℚ) := by
  obtain ⟨L, hL, R, hR, hLR_eq⟩ := Gamma0_T_diag_rep_decompose N a ha hgcd
  obtain ⟨σL, hσL⟩ := Gamma0_le_SLnZ N hL
  obtain ⟨σR, hσR⟩ := Gamma0_le_SLnZ N hR
  rw [hLR_eq, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  rw [show (L : Matrix (Fin 2) (Fin 2) ℚ).det = 1 by
        rw [show (L : GL _ ℚ) = (σL : GL _ ℚ) from hσL.symm]
        exact HeckeRing.GL2.SLnZ_to_GLnQ_det σL,
      show (R : Matrix (Fin 2) (Fin 2) ℚ).det = 1 by
        rw [show (R : GL _ ℚ) = (σR : GL _ ℚ) from hσR.symm]
        exact HeckeRing.GL2.SLnZ_to_GLnQ_det σR,
      diagMat_det 2 a ha]
  push_cast; simp [Fin.prod_univ_two]

/-- **Witness lemma**: `T'(1, p^(k+1))` is in the Γ₀(N)-mulSupport of
    `(rep T'(1, p), rep T'(1, p^k))`. Mirror of `D_out1_pp_in_mulSupport`. -/
private lemma D_out1_Gamma0_pp_in_mulSupport (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ).gcd N = 1) (k : ℕ) (hk : 1 ≤ k) :
    (T_diag_Gamma0 N (![1, p^(k+1)])
        (fun i => by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)) ∈
      HeckeRing.mulSupport (Gamma0_pair N)
        (HeckeCoset.rep (T_diag_Gamma0 N (![1, p])
          (fun i => by fin_cases i <;> simp [hp.pos]) (by simp)))
        (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k])
          (fun i => by fin_cases i <;> simp [pow_pos hp.pos]) (by simp))) := by
  set H := (Gamma0_pair N).H
  have h_pos1 : ∀ i : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hp.pos]
  have h_pos2 : ∀ i : Fin 2, 0 < (![1, p^k] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [pow_pos hp.pos]
  have h_pos3 : ∀ i : Fin 2, 0 < (![1, p^(k+1)] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [pow_pos hp.pos]
  obtain ⟨L₁, hL₁, R₁, hR₁, hα_eq⟩ :=
    Gamma0_T_diag_rep_decompose N (![1, p]) h_pos1 (by simp)
  obtain ⟨L₂, hL₂, R₂, hR₂, hβ_eq⟩ :=
    Gamma0_T_diag_rep_decompose N (![1, p^k]) h_pos2 (by simp)
  apply HeckeRing.mem_mulSupport_of_product_mem _ _ _
    ⟨diagMat 2 (![1, p^(k+1)]), diagMat_mem_Delta0_of_gcd N _ h_pos3 (by simp)⟩
    ⟨L₁⁻¹, H.inv_mem hL₁⟩
    ⟨R₁⁻¹ * L₂⁻¹, H.mul_mem (H.inv_mem hR₁) (H.inv_mem hL₂)⟩
  show (L₁⁻¹ : GL (Fin 2) ℚ) *
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) h_pos1 (by simp)) : GL (Fin 2) ℚ) *
      ((R₁⁻¹ * L₂⁻¹ : GL (Fin 2) ℚ) *
        (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) h_pos2 (by simp)) :
          GL (Fin 2) ℚ)) ∈
    DoubleCoset.doubleCoset (diagMat 2 (![1, p^(k+1)]) : GL (Fin 2) ℚ)
      (H : Set _) (H : Set _)
  rw [hα_eq, hβ_eq, DoubleCoset.mem_doubleCoset]
  refine ⟨1, H.one_mem, R₂, hR₂, ?_⟩
  -- L₁⁻¹ * (L₁ * D₁ * R₁) * ((R₁⁻¹ * L₂⁻¹) * (L₂ * D₂ * R₂)) = D₁ * D₂ * R₂
  have h_alg : (L₁⁻¹ : GL (Fin 2) ℚ) * (L₁ * diagMat 2 (![1, p]) * R₁) *
      ((R₁⁻¹ * L₂⁻¹ : GL (Fin 2) ℚ) * (L₂ * diagMat 2 (![1, p^k]) * R₂)) =
      diagMat 2 (![1, p]) * diagMat 2 (![1, p^k]) * R₂ := by group
  rw [h_alg]
  rw [diagMat_mul 2 (![1, p]) (![1, p^k]) h_pos1 h_pos2]
  rw [show (1 : GL (Fin 2) ℚ) * diagMat 2 (![1, p^(k+1)]) * R₂ =
      diagMat 2 (![1, p^(k+1)]) * R₂ from by group]
  congr 2
  ext i; fin_cases i <;> simp [Pi.mul_apply, pow_succ, mul_comm]

/-- **Support inclusion at Γ₀(N) level**:
    Any A in mulSupport(rep T'(1,p), rep T'(1,p^k)) at Γ₀(N) equals T'(1, p^(k+1)) or T'(p, p^k). -/
private lemma mulSupport_Gamma0_pp_subset (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ).gcd N = 1) (k : ℕ) (hk : 1 ≤ k)
    (A : HeckeCoset (Gamma0_pair N))
    (hA : A ∈ HeckeRing.mulSupport (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p])
        (fun i => by fin_cases i <;> simp [hp.pos]) (by simp)))
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k])
        (fun i => by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)))) :
    A = T_diag_Gamma0 N (![1, p^(k+1)])
        (fun i => by fin_cases i <;> simp [pow_pos hp.pos]) (by simp) ∨
    A = T_diag_Gamma0 N (![p, p^k])
        (fun i => by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
        (by show Int.gcd (↑p) ↑N = 1; exact hpN) := by
  set H := (Gamma0_pair N).H
  have h_pos1 : ∀ i : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hp.pos]
  have h_pos2 : ∀ i : Fin 2, 0 < (![1, p^k] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [pow_pos hp.pos]
  obtain ⟨a, ha_pos, ha_gcd, ha_div, hrep⟩ := Gamma0_exists_diag_rep N (HeckeCoset.rep A)
  have hA_eq : A = T_diag_Gamma0 N a ha_pos ha_gcd := by
    rw [← hrep]; exact (HeckeCoset.mk_rep A).symm
  have h_a_div : DivChain 2 a := fun i hi => (show i = 0 by omega) ▸ ha_div
  rw [HeckeRing.mulSupport] at hA
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists] at hA
  obtain ⟨i₀, j₀, hmap⟩ := hA
  obtain ⟨L₁, hL₁, R₁, hR₁, hα_eq⟩ :=
    Gamma0_T_diag_rep_decompose N (![1, p]) h_pos1 (by simp)
  obtain ⟨L₂, hL₂, R₂, hR₂, hβ_eq⟩ :=
    Gamma0_T_diag_rep_decompose N (![1, p^k]) h_pos2 (by simp)
  have h_prod_in_A_Γ₀ : ((i₀.out : GL (Fin 2) ℚ)) *
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) h_pos1 (by simp)) : GL (Fin 2) ℚ) *
      (((j₀.out : GL (Fin 2) ℚ)) *
        (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) h_pos2 (by simp)) :
          GL (Fin 2) ℚ)) ∈
      DoubleCoset.doubleCoset (diagMat 2 a : GL (Fin 2) ℚ) (H : Set _) (H : Set _) := by
    have h1 : ((i₀.out : GL (Fin 2) ℚ)) *
        (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) h_pos1 (by simp)) : GL (Fin 2) ℚ) *
        (((j₀.out : GL (Fin 2) ℚ)) *
          (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) h_pos2 (by simp)) :
            GL (Fin 2) ℚ)) ∈
        HeckeCoset.toSet (HeckeRing.mulMap (Gamma0_pair N)
          (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) h_pos1 (by simp)))
          (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) h_pos2 (by simp))) (i₀, j₀)) := by
      rw [HeckeRing.mulMap, HeckeCoset.toSet_mk]
      exact DoubleCoset.mem_doubleCoset_self _ _ _
    rw [hmap, hA_eq, T_diag_Gamma0, HeckeCoset.toSet_mk] at h1
    exact h1
  have h_prod_in_SL := Gamma0_doubleCoset_subset_Gamma N _ h_prod_in_A_Γ₀
  rw [DoubleCoset.mem_doubleCoset] at h_prod_in_SL
  obtain ⟨L_a, ⟨SL_La, rfl⟩, R_a, ⟨SL_Ra, rfl⟩, h_prod_eq⟩ := h_prod_in_SL
  obtain ⟨SL_L₁, hSL_L₁⟩ := Gamma0_le_SLnZ N hL₁
  obtain ⟨SL_R₁, hSL_R₁⟩ := Gamma0_le_SLnZ N hR₁
  obtain ⟨SL_L₂, hSL_L₂⟩ := Gamma0_le_SLnZ N hL₂
  obtain ⟨SL_R₂, hSL_R₂⟩ := Gamma0_le_SLnZ N hR₂
  obtain ⟨SL_i₀, hSL_i₀⟩ := Gamma0_le_SLnZ N (SetLike.coe_mem i₀.out)
  obtain ⟨SL_j₀, hSL_j₀⟩ := Gamma0_le_SLnZ N (SetLike.coe_mem j₀.out)
  have hD1_eq_SL : (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) h_pos1 (by simp)) : GL (Fin 2) ℚ) =
      (SL_L₁ : GL (Fin 2) ℚ) * diagMat 2 (![1, p]) * (SL_R₁ : GL (Fin 2) ℚ) := by
    rw [hα_eq, hSL_L₁, hSL_R₁]
  have hD2_eq_SL : (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) h_pos2 (by simp)) :
      GL (Fin 2) ℚ) =
      (SL_L₂ : GL (Fin 2) ℚ) * diagMat 2 (![1, p^k]) * (SL_R₂ : GL (Fin 2) ℚ) := by
    rw [hβ_eq, hSL_L₂, hSL_R₂]
  have h_det := HeckeRing.GL2.mulSupport_pp_det_eq p k a ha_pos
    (i₀.out : GL (Fin 2) ℚ)
    (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) h_pos1 (by simp)) : GL (Fin 2) ℚ)
    (j₀.out : GL (Fin 2) ℚ)
    (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) h_pos2 (by simp)) : GL (Fin 2) ℚ)
    (by rw [show ((i₀.out : H) : GL (Fin 2) ℚ) = (SL_i₀ : GL (Fin 2) ℚ) from hSL_i₀.symm]
        exact HeckeRing.GL2.SLnZ_to_GLnQ_det SL_i₀)
    (by have := Gamma0_T_diag_rep_det N (![1, p]) h_pos1 (by simp)
        push_cast at this; rw [this]; ring)
    (by rw [show ((j₀.out : H) : GL (Fin 2) ℚ) = (SL_j₀ : GL (Fin 2) ℚ) from hSL_j₀.symm]
        exact HeckeRing.GL2.SLnZ_to_GLnQ_det SL_j₀)
    (by have := Gamma0_T_diag_rep_det N (![1, p^k]) h_pos2 (by simp)
        push_cast at this; rw [this]; ring)
    SL_La SL_Ra h_prod_eq
  have h_dvd := HeckeRing.GL2.mulSupport_pp_dvd_p p hp k hk a ha_pos h_a_div
    (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) h_pos1 (by simp)) : GL (Fin 2) ℚ)
    (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) h_pos2 (by simp)) : GL (Fin 2) ℚ)
    (i₀.out : GL (Fin 2) ℚ) (j₀.out : GL (Fin 2) ℚ)
    SL_L₁ SL_R₁ SL_L₂ SL_R₂ SL_La SL_Ra SL_i₀ SL_j₀
    hD1_eq_SL hD2_eq_SL hSL_i₀.symm hSL_j₀.symm h_prod_eq
  have h_GL := HeckeRing.GL2.mulSupport_pp_case_split p hp k hk a ha_pos h_a_div h_det h_dvd
  have h_pos_out1 : ∀ i : Fin 2, 0 < (![1, p^(k+1)] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [pow_pos hp.pos]
  have h_pos_out2 : ∀ i : Fin 2, 0 < (![p, p^k] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hp.pos, pow_pos hp.pos]
  have h_pN_cop : Nat.Coprime p N := by
    rwa [Int.gcd_natCast_natCast] at hpN
  have h_a_coprime_det : Nat.Coprime (a 0 * a 1) N := by
    rw [h_det]; exact h_pN_cop.pow_left _
  have h_CD_a : CoprimeDet N ⟨diagMat 2 a, diagMat_mem_Delta0_of_gcd N a ha_pos ha_gcd⟩ := by
    intro A' hA'
    have h_det_eq : (A'.det : ℚ) = (a 0 * a 1 : ℕ) := by
      rw [show (A'.det : ℚ) = (A'.map (Int.cast : ℤ → ℚ)).det from
        (det_intMat_cast 2 A').symm, ← hA']
      show (diagMat 2 a : GL (Fin 2) ℚ).val.det = _
      rw [diagMat_det 2 a ha_pos]
      push_cast; rw [Fin.prod_univ_two]
    have h_A'_det : A'.det = (a 0 * a 1 : ℕ) := by exact_mod_cast h_det_eq
    rw [h_A'_det]
    show Int.gcd ((a 0 * a 1 : ℕ) : ℤ) ↑N = 1
    rw [Int.gcd_natCast_natCast]; exact_mod_cast h_a_coprime_det
  rcases h_GL with h_out1_GL | h_out2_GL
  · left
    rw [hA_eq]
    have h_CD_out1 : CoprimeDet N ⟨diagMat 2 (![1, p^(k+1)]),
        diagMat_mem_Delta0_of_gcd N _ h_pos_out1 (by simp)⟩ := by
      intro A' hA'
      have h_det_eq : (A'.det : ℚ) = (p : ℚ)^(k+1) := by
        rw [show (A'.det : ℚ) = (A'.map (Int.cast : ℤ → ℚ)).det from
          (det_intMat_cast 2 A').symm, ← hA']
        show (diagMat 2 (![1, p^(k+1)] : Fin 2 → ℕ) : GL (Fin 2) ℚ).val.det = _
        rw [diagMat_det 2 _ h_pos_out1]
        push_cast; rw [Fin.prod_univ_two]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      have h_A'_det : A'.det = (p^(k+1) : ℕ) := by exact_mod_cast h_det_eq
      rw [h_A'_det, Int.gcd_natCast_natCast]
      exact h_pN_cop.pow_left _
    have h_coset_eq : cosetMap N
        (T_diag_Gamma0 N a ha_pos ha_gcd) =
      cosetMap N
        (T_diag_Gamma0 N (![1, p^(k+1)]) h_pos_out1 (by simp)) := by
      rw [cosetMap_T_diag_Gamma0, cosetMap_T_diag_Gamma0]
      exact h_out1_GL
    apply shimura_prop_3_31 N
      ⟨diagMat 2 a, diagMat_mem_Delta0_of_gcd N a ha_pos ha_gcd⟩
      ⟨diagMat 2 (![1, p^(k+1)]), diagMat_mem_Delta0_of_gcd N _ h_pos_out1 (by simp)⟩
      h_CD_a h_CD_out1 h_coset_eq
  · right
    rw [hA_eq]
    have h_CD_out2 : CoprimeDet N ⟨diagMat 2 (![p, p^k]),
        diagMat_mem_Delta0_of_gcd N _ h_pos_out2 (by show Int.gcd (↑p) ↑N = 1; exact hpN)⟩ := by
      intro A' hA'
      have h_det_eq : (A'.det : ℚ) = ((p^(k+1) : ℕ) : ℚ) := by
        rw [show (A'.det : ℚ) = (A'.map (Int.cast : ℤ → ℚ)).det from
          (det_intMat_cast 2 A').symm, ← hA']
        show (diagMat 2 (![p, p^k] : Fin 2 → ℕ) : GL (Fin 2) ℚ).val.det = _
        rw [diagMat_det 2 _ h_pos_out2]
        push_cast; rw [Fin.prod_univ_two]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [show k + 1 = 1 + k from by ring, pow_add, pow_one]
      have h_A'_det : A'.det = (p^(k+1) : ℕ) := by exact_mod_cast h_det_eq
      rw [h_A'_det, Int.gcd_natCast_natCast]
      exact h_pN_cop.pow_left _
    have h_coset_eq : cosetMap N
        (T_diag_Gamma0 N a ha_pos ha_gcd) =
      cosetMap N
        (T_diag_Gamma0 N (![p, p^k]) h_pos_out2 (by show Int.gcd (↑p) ↑N = 1; exact hpN)) := by
      rw [cosetMap_T_diag_Gamma0, cosetMap_T_diag_Gamma0]
      exact h_out2_GL
    apply shimura_prop_3_31 N
      ⟨diagMat 2 a, diagMat_mem_Delta0_of_gcd N a ha_pos ha_gcd⟩
      ⟨diagMat 2 (![p, p^k]),
        diagMat_mem_Delta0_of_gcd N _ h_pos_out2 (by show Int.gcd (↑p) ↑N = 1; exact hpN)⟩
      h_CD_a h_CD_out2 h_coset_eq

set_option maxHeartbeats 800000 in
/-- **Multiplicity values at Γ₀(N) level**:
    `μ(D'_out1) = 1` and `μ(D'_out2) = c_k` (where c_k = p+1 if k=1, else p). -/
private lemma heckeMultiplicity_Gamma0_values (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ).gcd N = 1) (k : ℕ) (hk : 1 ≤ k) :
    HeckeRing.heckeMultiplicity (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p])
        (fun i => by fin_cases i <;> simp [hp.pos]) (by simp)))
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k])
        (fun i => by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)))
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^(k+1)])
        (fun i => by fin_cases i <;> simp [pow_pos hp.pos]) (by simp))) = 1 ∧
    HeckeRing.heckeMultiplicity (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p])
        (fun i => by fin_cases i <;> simp [hp.pos]) (by simp)))
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k])
        (fun i => by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)))
      (HeckeCoset.rep (T_diag_Gamma0 N (![p, p^k])
        (fun i => by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
        (by show Int.gcd (↑p) ↑N = 1; exact hpN))) =
      if k = 1 then ((p : ℤ) + 1) else (p : ℤ) := by
  have h_pN_cop : Nat.Coprime p N := by rwa [Int.gcd_natCast_natCast] at hpN
  set D1 := T_diag_Gamma0 N (![1, p])
    (fun i => by fin_cases i <;> simp [hp.pos]) (by simp)
  set D2 := T_diag_Gamma0 N (![1, p^k])
    (fun i => by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)
  set D_out1 := T_diag_Gamma0 N (![1, p^(k+1)])
    (fun i => by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)
  set D_out2 := T_diag_Gamma0 N (![p, p^k])
    (fun i => by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
    (by show Int.gcd (↑p) ↑N = 1; exact hpN)
  set m1 := HeckeRing.heckeMultiplicity (Gamma0_pair N) D1.rep D2.rep D_out1.rep
  set m2 := HeckeRing.heckeMultiplicity (Gamma0_pair N) D1.rep D2.rep D_out2.rep
  have h_ne : D_out1 ≠ D_out2 := by
    intro heq
    have h_GL_eq : cosetMap N D_out1 = cosetMap N D_out2 := congr_arg _ heq
    rw [cosetMap_T_diag_Gamma0, cosetMap_T_diag_Gamma0] at h_GL_eq
    have h1_pos : ∀ i : Fin 2, 0 < (![1, p ^ (k + 1)]) i := by
      intro i; fin_cases i <;> simp [pow_pos hp.pos]
    have h2_pos : ∀ i : Fin 2, 0 < (![p, p ^ k]) i := by
      intro i; fin_cases i <;> simp [hp.pos, pow_pos hp.pos]
    have h1_div : DivChain 2 (![1, p ^ (k + 1)]) := fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0; simp
    have h2_div : DivChain 2 (![p, p ^ k]) := fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0; simpa using dvd_pow_self p (show k ≠ 0 by omega)
    have := congr_fun (diagonal_representative_unique 2 _ _ h1_pos h2_pos h1_div h2_div h_GL_eq) 0
    simp [Matrix.cons_val_zero] at this
    exact absurd this.symm (Nat.Prime.one_lt hp).ne'
  have h_zero : ∀ A, A ≠ D_out1 → A ≠ D_out2 →
      HeckeRing.heckeMultiplicity (Gamma0_pair N) D1.rep D2.rep
        (HeckeCoset.rep A) = 0 := by
    intro A h1 h2
    apply HeckeRing.heckeMultiplicity_eq_zero_of_nmem_mulSupport
    intro hmem
    exact (mulSupport_Gamma0_pp_subset N p hp hpN k hk A hmem).elim h1 h2
  have h_deg : m1 * HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out1 +
      m2 * HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out2 =
      HeckeRing.HeckeCoset_deg (Gamma0_pair N) D1 *
        HeckeRing.HeckeCoset_deg (Gamma0_pair N) D2 :=
    HeckeRing.heckeMultiplicity_deg_sum_eq (Gamma0_pair N) D1 D2 D_out1 D_out2 h_ne h_zero
  -- Substitute degree formulas
  have h_deg_D1 := HeckeCoset_deg_Gamma0_one_ppow N p hp h_pN_cop 1 (by omega)
  simp only [pow_one, show (1 - 1 : ℕ) = 0 from rfl, pow_zero, one_mul] at h_deg_D1
  -- D2 := T_diag_Gamma0 (![1, p^k]); the lemma uses (![1, p^k]) form
  have h_deg_D2 := HeckeCoset_deg_Gamma0_one_ppow N p hp h_pN_cop k hk
  have h_deg_out1 := HeckeCoset_deg_Gamma0_one_ppow N p hp h_pN_cop (k+1) (by omega)
  have h_deg_out2 := HeckeCoset_deg_Gamma0_p_ppow N p hp h_pN_cop k hk
  have h_D1_eq : D1 = T_diag_Gamma0 N (![1, p^1])
      (fun i => by fin_cases i <;> simp [hp.pos]) (by simp) := by
    show T_diag_Gamma0 N (![1, p]) _ _ = _
    congr 1
    funext i; fin_cases i <;> simp
  rw [show HeckeRing.HeckeCoset_deg (Gamma0_pair N) D1 = ↑((p + 1 : ℕ) : ℤ) by
        rw [h_D1_eq]
        have := HeckeCoset_deg_Gamma0_one_ppow N p hp h_pN_cop 1 (by omega)
        push_cast at this ⊢
        push_cast
        convert this using 1
        push_cast; ring] at h_deg
  rw [h_deg_D2] at h_deg
  rw [h_deg_out1] at h_deg
  rw [h_deg_out2] at h_deg
  have hm1_nn := HeckeRing.heckeMultiplicity_nonneg (Gamma0_pair N) D1.rep D2.rep D_out1.rep
  have hm2_nn := HeckeRing.heckeMultiplicity_nonneg (Gamma0_pair N) D1.rep D2.rep D_out2.rep
  have hm1_pos : 1 ≤ m1 := by
    have hne : (HeckeRing.m (Gamma0_pair N) D1.rep D2.rep) D_out1 ≠ 0 := by
      rw [← Finsupp.mem_support_iff, HeckeRing.m_support]
      exact D_out1_Gamma0_pp_in_mulSupport N p hp hpN k hk
    exact Int.lt_iff_add_one_le.mp (lt_of_le_of_ne hm1_nn (Ne.symm hne))
  by_cases hk1 : k = 1
  · subst hk1
    simp only [if_true, show (1 - 1 : ℕ) = 0 from rfl, pow_zero, one_mul,
      Nat.add_sub_cancel] at h_deg ⊢
    push_cast at h_deg ⊢
    have h_m1_eq : m1 = 1 := by
      nlinarith [hm2_nn, mul_self_nonneg ((p : ℤ) - 1),
        show (2 : ℤ) ≤ p from by exact_mod_cast hp.two_le]
    refine ⟨h_m1_eq, ?_⟩
    rw [h_m1_eq] at h_deg
    linarith
  · simp only [if_neg hk1] at h_deg ⊢
    have hk2 : 2 ≤ k := by omega
    push_cast at h_deg ⊢
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    have hpk : (p : ℤ) ^ k = (p : ℤ) ^ (k - 2) * (p : ℤ) ^ 2 := by
      exact_mod_cast show (p : ℕ) ^ k = p ^ (k - 2) * p ^ 2 by
        rw [← pow_add]; congr 1; omega
    have hpk1 : (p : ℤ) ^ (k - 1) = (p : ℤ) ^ (k - 2) * p := by
      have : (p : ℕ) ^ (k - 1) = p ^ (k - 2) * p ^ 1 := by
        rw [← pow_add]; congr 1; omega
      simp only [pow_one] at this; exact_mod_cast this
    have hpk_succ : (p : ℤ)^k = ((p^k : ℕ) : ℤ) := by push_cast; rfl
    have hpkm1 : ((p^(k-1) : ℕ) : ℤ) = (p : ℤ)^(k-1) := by push_cast; rfl
    have hpkm2 : ((p^(k-2) : ℕ) : ℤ) = (p : ℤ)^(k-2) := by push_cast; rfl
    push_cast [hpkm1, hpkm2] at h_deg
    have h_eq : m1 * (p : ℤ) ^ 2 + m2 = (p : ℤ) * ((p : ℤ) + 1) := by
      have h := h_deg
      rw [hpk, hpk1] at h
      have key : (p : ℤ) ^ (k - 2) * ((p : ℤ) + 1) ≠ 0 := by positivity
      have := mul_right_cancel₀ key (show
        (m1 * (p : ℤ) ^ 2 + m2) * ((p : ℤ) ^ (k - 2) * ((p : ℤ) + 1)) =
        ((p : ℤ) * ((p : ℤ) + 1)) * ((p : ℤ) ^ (k - 2) * ((p : ℤ) + 1)) by nlinarith)
      linarith
    have h_m1_eq : m1 = 1 := by
      have h_le : m1 * (p : ℤ) ^ 2 ≤ (p : ℤ) ^ 2 + p := by linarith [h_eq, hm2_nn]
      nlinarith [show (p : ℤ) ^ 2 ≥ 4 by nlinarith]
    refine ⟨h_m1_eq, ?_⟩
    rw [h_m1_eq] at h_eq
    linarith

/-- **Gamma0-level prime-power multiplication formula** (p ∤ N case).
    For prime p coprime to N and k ≥ 1:
    `T'(1,p) * T'(1, p^k) = T'(1, p^(k+1)) + c_k • T'(p, p^k)`
    where c_k = p+1 if k=1, p if k ≥ 2.

    This is the Gamma0-level analogue of `T_sum_prime_mul_T_ad` (Shimura 3.24(5)).
    Per Shimura's *Introduction to the Arithmetic Theory of Automorphic Functions*
    p. 71. Mirrors the GL proof, transferring degrees and multiplicities via
    `cosetMap` + Proposition 3.31 injectivity. -/
private lemma Gamma0_T1p_mul_T1ppow_coprime (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ).gcd N = 1) (k : ℕ) (hk : 1 ≤ k) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p])
        (fun i => by fin_cases i <;> simp [hp.pos])
        (by simp)) 1 *
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p^k])
        (fun i => by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p^(k+1)])
        (fun i => by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) 1 +
    (if k = 1 then ((p : ℤ) + 1) else (p : ℤ)) •
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![p, p^k])
        (fun i => by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
        (by show Int.gcd (↑p) ↑N = 1; exact hpN)) 1 := by
  set D1 := T_diag_Gamma0 N (![1, p])
    (fun i => by fin_cases i <;> simp [hp.pos]) (by simp)
  set D2 := T_diag_Gamma0 N (![1, p^k])
    (fun i => by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)
  set D_out1 := T_diag_Gamma0 N (![1, p^(k+1)])
    (fun i => by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)
  set D_out2 := T_diag_Gamma0 N (![p, p^k])
    (fun i => by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
    (by show Int.gcd (↑p) ↑N = 1; exact hpN)
  set c : ℤ := if k = 1 then ((p : ℤ) + 1) else (p : ℤ)
  -- Show D_out1 ≠ D_out2 (same as in helper)
  have h_ne : D_out1 ≠ D_out2 := by
    intro heq
    have h_GL_eq : cosetMap N D_out1 = cosetMap N D_out2 := congr_arg _ heq
    rw [cosetMap_T_diag_Gamma0, cosetMap_T_diag_Gamma0] at h_GL_eq
    have h1_pos : ∀ i : Fin 2, 0 < (![1, p ^ (k + 1)]) i := by
      intro i; fin_cases i <;> simp [pow_pos hp.pos]
    have h2_pos : ∀ i : Fin 2, 0 < (![p, p ^ k]) i := by
      intro i; fin_cases i <;> simp [hp.pos, pow_pos hp.pos]
    have h1_div : DivChain 2 (![1, p ^ (k + 1)]) := fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0; simp
    have h2_div : DivChain 2 (![p, p ^ k]) := fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0; simpa using dvd_pow_self p (show k ≠ 0 by omega)
    have := congr_fun (diagonal_representative_unique 2 _ _
      h1_pos h2_pos h1_div h2_div h_GL_eq) 0
    simp [Matrix.cons_val_zero] at this
    exact absurd this.symm (Nat.Prime.one_lt hp).ne'
  have h_mul : HeckeRing.T_single (Gamma0_pair N) ℤ D1 1 *
      HeckeRing.T_single (Gamma0_pair N) ℤ D2 1 =
      HeckeRing.m (Gamma0_pair N) (HeckeCoset.rep D1) (HeckeCoset.rep D2) :=
    HeckeRing.T_single_one_mul_T_single_one (Gamma0_pair N) D1 D2
  rw [h_mul]
  show HeckeRing.m (Gamma0_pair N) D1.rep D2.rep =
      HeckeRing.T_single (Gamma0_pair N) ℤ D_out1 1 +
      c • HeckeRing.T_single (Gamma0_pair N) ℤ D_out2 1
  have h_rhs : HeckeRing.T_single (Gamma0_pair N) ℤ D_out1 1 +
      c • HeckeRing.T_single (Gamma0_pair N) ℤ D_out2 1 =
      Finsupp.single D_out1 1 + c • Finsupp.single D_out2 1 := rfl
  rw [h_rhs, Finsupp.smul_single', mul_one]
  apply Finsupp.ext; intro A
  show HeckeRing.heckeMultiplicity (Gamma0_pair N) D1.rep D2.rep (HeckeCoset.rep A) =
    (Finsupp.single D_out1 (1 : ℤ) + Finsupp.single D_out2 c) A
  rw [Finsupp.add_apply]
  by_cases h1 : A = D_out1
  · subst h1
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne h_ne, add_zero]
    exact (heckeMultiplicity_Gamma0_values N p hp hpN k hk).1
  · by_cases h2 : A = D_out2
    · subst h2
      rw [Finsupp.single_eq_of_ne (Ne.symm h_ne), Finsupp.single_eq_same, zero_add]
      exact (heckeMultiplicity_Gamma0_values N p hp hpN k hk).2
    · rw [Finsupp.single_eq_of_ne h1, Finsupp.single_eq_of_ne h2, add_zero]
      apply HeckeRing.heckeMultiplicity_eq_zero_of_nmem_mulSupport
      intro hmem
      exact (mulSupport_Gamma0_pp_subset N p hp hpN k hk A hmem).elim h1 h2

/-- **T'(1,m) ∈ range(ψ)** by strong induction on m (Shimura Thm 3.34 core).
Handles: m=1 (identity), m=p prime (generator), coprime products (T_coprime_mul),
p|N prime powers (T_bad_mul), non-prime-power composites (factorization + coprime mul).
The case p∤N, k≥2 uses `Gamma0_T1p_mul_T1ppow_coprime` to extract T'(1, p^k) from the
product T'(1,p) * T'(1, p^{k-1}) by subtraction. -/
private lemma T_1m_mem_ψ_range (m : ℕ) (hm : 0 < m) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m])
        (fun i => by fin_cases i <;> simp [hm])
        (by simp)) 1 ∈ (ψ_hom N).range := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
  by_cases hm1 : m = 1
  · subst hm1; convert (ψ_hom N).range.one_mem using 1
    show HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N ![1, 1] (fun i => by fin_cases i <;> simp) (by simp)) 1 = 1
    rw [HeckeRing.one_def]
    show (Finsupp.single _ (1 : ℤ) : HeckeRing.𝕋 (Gamma0_pair N) ℤ) =
         Finsupp.single (HeckeCoset.one _) 1
    congr 1
    -- T_diag_Gamma0 N ![1,1] = HeckeCoset.one (Gamma0_pair N)
    show (⟦⟨diagMat 2 (![1, 1] : Fin 2 → ℕ), _⟩⟧ : HeckeCoset _) =
         HeckeCoset.one (Gamma0_pair N)
    show (⟦⟨diagMat 2 (![1, 1] : Fin 2 → ℕ), _⟩⟧ : HeckeCoset _) =
         ⟦⟨(1 : GL (Fin 2) ℚ), _⟩⟧
    apply Quotient.sound
    show DoubleCoset.doubleCoset
        (⟨diagMat 2 (![1, 1] : Fin 2 → ℕ), _⟩ : (Gamma0_pair N).Δ).1
        ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) =
        DoubleCoset.doubleCoset
        (⟨(1 : GL (Fin 2) ℚ), _⟩ : (Gamma0_pair N).Δ).1
        ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _)
    have h_one : (diagMat 2 (![1, 1] : Fin 2 → ℕ) : GL (Fin 2) ℚ) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [diagMat, Matrix.diagonal, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.head_cons, Matrix.one_apply]
    show DoubleCoset.doubleCoset (diagMat 2 ![1, 1]) _ _ = DoubleCoset.doubleCoset 1 _ _
    rw [h_one]
  · obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    set q := m / p with hq_def
    have hpq : m = p * q := (Nat.mul_div_cancel' hp_dvd).symm
    have hq_pos : 0 < q := Nat.pos_of_ne_zero
      (by intro h; rw [h, Nat.mul_zero] at hpq; omega)
    have hq_lt : q < m := by
      rw [hpq]; exact lt_mul_of_one_lt_left hq_pos hp.one_lt
    by_cases hcop : Nat.Coprime p q
    · by_cases hq1 : q = 1
      · have h_m_eq_p : m = p := by rw [hpq, hq1, mul_one]
        refine ⟨MvPolynomial.X (⟨p, hp⟩, (0 : Fin 2)), ?_⟩
        show ψ_hom N (MvPolynomial.X (⟨p, hp⟩, (0 : Fin 2))) = _
        simp only [ψ_hom, MvPolynomial.eval₂Hom_X', ↓reduceIte]
        congr 1
        show T_diag_Gamma0 N (![1, p] : Fin 2 → ℕ) _ _ = T_diag_Gamma0 N ![1, m] _ _
        congr 1; funext i; fin_cases i
        · rfl
        · show p = m; exact h_m_eq_p.symm
      have hp_lt : p < m := by
        rw [hpq]; exact lt_mul_of_one_lt_right hp.pos (by omega)
      have h_IHp := ih p hp_lt hp.pos
      have h_IHq := ih q hq_lt hq_pos
      have h_combine := (ψ_hom N).range.mul_mem h_IHp h_IHq
      rw [T_coprime_mul N p q hp.pos hq_pos hcop] at h_combine
      have h_replace : T_diag_Gamma0 N (![1, p * q] : Fin 2 → ℕ)
            (fun i => by fin_cases i <;> simp [Nat.mul_pos hp.pos hq_pos])
            (by simp) =
          T_diag_Gamma0 N (![1, m] : Fin 2 → ℕ)
            (fun i => by fin_cases i <;> simp [hm]) (by simp) := by
        congr 1
        funext i; fin_cases i
        · rfl
        · show p * q = m; exact hpq.symm
      rw [h_replace] at h_combine
      exact h_combine
    · by_cases hm_ppow : ∃ k, m = p ^ k
      · obtain ⟨k, rfl⟩ := hm_ppow
        have hk : 2 ≤ k := by
          by_contra h
          push_neg at h
          interval_cases k
          · exact hm1 rfl
          · apply hcop
            have hq_eq : q = 1 := by
              rw [hq_def, pow_one, Nat.div_self hp.pos]
            rw [hq_eq]
            exact Nat.coprime_one_right p
        by_cases hpN : (p : ℤ).gcd N = 1
        · have hp_lt : p < p ^ k := by
            calc p = p ^ 1 := (pow_one p).symm
              _ < p ^ k := Nat.pow_lt_pow_right hp.one_lt hk
          have hpk1_lt : p ^ (k - 1) < p ^ k :=
            Nat.pow_lt_pow_right hp.one_lt (by omega)
          have hpk2_lt : p ^ (k - 2) < p ^ k :=
            Nat.pow_lt_pow_right hp.one_lt (by omega)
          have h_IHp := ih p hp_lt hp.pos
          have h_IHpk1 := ih (p ^ (k - 1)) hpk1_lt (pow_pos hp.pos _)
          have h_IHpk2 := ih (p ^ (k - 2)) hpk2_lt (pow_pos hp.pos _)
          have hk1_pos : 1 ≤ k - 1 := by omega
          have h_IHpk1_alt : HeckeRing.T_single (Gamma0_pair N) ℤ
              (T_diag_Gamma0 N (![1, p^((k-1)-1)])
                (fun i => by fin_cases i <;> simp [pow_pos hp.pos])
                (by simp)) 1 ∈ (ψ_hom N).range := by
            have h_eq : k - 1 - 1 = k - 2 := by omega
            rw [h_eq]; exact h_IHpk2
          have h_Tppk1 := T_p_ppow_mem_ψ_range N p hp hpN (k - 1) hk1_pos h_IHpk1_alt
          have h_formula := Gamma0_T1p_mul_T1ppow_coprime N p hp hpN (k - 1) hk1_pos
          have hk_norm : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
          rw [hk_norm] at h_formula
          rw [eq_sub_of_add_eq h_formula.symm]
          exact (ψ_hom N).range.sub_mem
            ((ψ_hom N).range.mul_mem h_IHp h_IHpk1)
            ((ψ_hom N).range.zsmul_mem h_Tppk1 _)
        · have hp_lt : p < p ^ k := by
            calc p = p ^ 1 := (pow_one p).symm
              _ < p ^ k := Nat.pow_lt_pow_right hp.one_lt hk
          have hpk1_lt : p ^ (k - 1) < p ^ k :=
            Nat.pow_lt_pow_right hp.one_lt (by omega)
          have h_IHp := ih p hp_lt hp.pos
          have h_IHpk1 := ih (p ^ (k - 1)) hpk1_lt (pow_pos hp.pos _)
          have hpN : ¬((p : ℤ).gcd ↑N = 1) := hpN
          have hp_dvd_N : p ∣ N := by
            by_contra h
            exact hpN (by rw [Int.gcd_natCast_natCast]; exact (hp.coprime_iff_not_dvd.mpr h))
          have h_pk_eq : p ^ k = p * p ^ (k - 1) := by
            rw [← pow_succ']; congr 1; omega
          have h_combine := (ψ_hom N).range.mul_mem h_IHp h_IHpk1
          rw [T_bad_mul N p (p ^ (k - 1)) hp.pos (pow_pos hp.pos _) 1
              (dvd_trans hp_dvd_N (dvd_pow_self N (by omega)))
              (k - 1) (pow_dvd_pow_of_dvd hp_dvd_N (k - 1))] at h_combine
          have h_replace : T_diag_Gamma0 N (![1, p * p ^ (k - 1)] : Fin 2 → ℕ)
                (fun i => by fin_cases i <;>
                  simp [Nat.mul_pos hp.pos (pow_pos hp.pos _)])
                (by simp) =
              T_diag_Gamma0 N (![1, p ^ k] : Fin 2 → ℕ)
                (fun i => by fin_cases i <;> simp [hm]) (by simp) := by
            congr 1
            funext i; fin_cases i
            · rfl
            · show p * p ^ (k - 1) = p ^ k; exact h_pk_eq.symm
          rw [h_replace] at h_combine
          exact h_combine
      · push_neg at hm_ppow
        set v := m.factorization p
        set a := p ^ v with ha_def
        set b := m / a with hb_def
        have ha_dvd : a ∣ m :=
          (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mpr le_rfl
        have hab : m = a * b := (Nat.mul_div_cancel' ha_dvd).symm
        have hv_pos : 0 < v := by
          rw [show v = m.factorization p from rfl]
          exact Nat.Prime.factorization_pos_of_dvd hp (by omega) hp_dvd
        have ha_pos : 0 < a := pow_pos hp.pos v
        have hb_pos : 0 < b := Nat.pos_of_ne_zero (by
          intro hb0; rw [hb0, Nat.mul_zero] at hab; omega)
        have ha_lt : a < m := by
          rw [hab]; refine lt_mul_of_one_lt_right ha_pos ?_
          by_contra h; push_neg at h
          have hb_one : b = 1 := by omega
          rw [hb_one, Nat.mul_one] at hab
          exact hm_ppow v hab
        have hb_lt : b < m := by
          rw [hab]; exact lt_mul_of_one_lt_left hb_pos (Nat.one_lt_pow hv_pos.ne' hp.one_lt)
        have hcop_ab : Nat.Coprime a b :=
          (Nat.Prime.coprime_pow_of_not_dvd hp
            (by simp [hb_def]; exact Nat.not_dvd_ordCompl hp (by omega))).symm
        have h_combine := (ψ_hom N).range.mul_mem (ih a ha_lt ha_pos) (ih b hb_lt hb_pos)
        rw [T_coprime_mul N a b ha_pos hb_pos hcop_ab] at h_combine
        have h_replace : T_diag_Gamma0 N (![1, a * b] : Fin 2 → ℕ)
              (fun i => by fin_cases i <;> simp [Nat.mul_pos ha_pos hb_pos])
              (by simp) =
            T_diag_Gamma0 N (![1, m] : Fin 2 → ℕ)
              (fun i => by fin_cases i <;> simp [hm]) (by simp) := by
          congr 1
          funext i; fin_cases i
          · rfl
          · show a * b = m; exact hab.symm
        rw [h_replace] at h_combine
        exact h_combine

/-- **T'(d₁,d₂) ∈ range(ψ)** for `d₁ | d₂`, `gcd(d₁,N) = 1`.
Reduces to `T_1m_mem_ψ_range` when `d₁ = 1`. The `d₁ > 1` case needs
Gamma0-level scalar extraction: `T'(d₁,d₂) = T'(d₁,d₁) * T'(1,d₂/d₁)`. -/
private lemma T_diag_mem_ψ_range (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1) (hdiv : a 0 ∣ a 1) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N a ha hgcd) 1 ∈ (ψ_hom N).range := by
  by_cases ha1 : a 0 = 1
  · -- d₁ = 1: direct from T_1m_mem_ψ_range
    have ha_eq : a = ![1, a 1] := by ext i; fin_cases i <;> simp [ha1]
    have : T_diag_Gamma0 N a ha hgcd = T_diag_Gamma0 N (![1, a 1])
        (fun i => by fin_cases i <;> simp [ha 1]) (by simp) := by
      congr 1
    rw [this]
    exact T_1m_mem_ψ_range N (a 1) (ha 1)
  · have ha0_gt : 1 < a 0 := by
      have := ha 0; omega
    set q := a 1 / a 0 with hq_def
    have hq_pos : 0 < q := by
      rw [hq_def]
      exact Nat.div_pos (Nat.le_of_dvd (ha 1) hdiv) (ha 0)
    have hq_mul : a 1 = a 0 * q := (Nat.mul_div_cancel' hdiv).symm
    have h_T1q := T_1m_mem_ψ_range N q hq_pos
    suffices hscalar : ∀ (d : ℕ) (hd : 0 < d) (hd_gcd : Int.gcd (↑d) ↑N = 1),
        HeckeRing.T_single (Gamma0_pair N) ℤ
          (T_diag_Gamma0 N (fun _ : Fin 2 => d) (fun _ => hd) hd_gcd) 1 ∈
          (ψ_hom N).range by
      have h_scalar_a0 := hscalar (a 0) (ha 0) hgcd
      have h_product := T_Gamma0_scalar_mul N (a 0) q (ha 0) hq_pos hgcd
      have hfun_eq : (fun _ : Fin 2 => a 0) * ![1, q] = a := by
        ext i; fin_cases i
        · simp [Pi.mul_apply]
        · simp [Pi.mul_apply, hq_mul]
      have hD_eq : T_diag_Gamma0 N ((fun _ : Fin 2 => a 0) * ![1, q])
          (fun i => Nat.mul_pos (ha 0) (by fin_cases i <;> simp [hq_pos]))
          (by show Int.gcd (↑(a 0 * 1)) ↑N = 1; simp [hgcd]) =
        T_diag_Gamma0 N a ha hgcd := by
        show (⟦⟨diagMat 2 ((fun _ : Fin 2 => a 0) * ![1, q]), _⟩⟧ : HeckeCoset _) =
             ⟦⟨diagMat 2 a, _⟩⟧
        congr 1
        apply Subtype.ext
        show diagMat 2 ((fun _ : Fin 2 => a 0) * ![1, q]) = diagMat 2 a
        rw [hfun_eq]
      rw [hD_eq] at h_product
      rw [← h_product]
      exact (ψ_hom N).range.mul_mem h_scalar_a0 h_T1q
    intro d
    induction d using Nat.strongRecOn with
    | _ d ih =>
    intro hd hd_gcd
    by_cases hd1 : d = 1
    · subst hd1
      convert (ψ_hom N).range.one_mem using 1
      show HeckeRing.T_single (Gamma0_pair N) ℤ
        (T_diag_Gamma0 N (fun _ : Fin 2 => 1) (fun _ => Nat.one_pos) hd_gcd) 1 = 1
      rw [HeckeRing.one_def]
      show (Finsupp.single _ (1 : ℤ) : HeckeRing.𝕋 (Gamma0_pair N) ℤ) =
           Finsupp.single (HeckeCoset.one _) 1
      congr 1
      show (⟦⟨diagMat 2 (fun _ : Fin 2 => 1), _⟩⟧ : HeckeCoset _) =
           ⟦⟨(1 : GL (Fin 2) ℚ), _⟩⟧
      apply Quotient.sound
      show DoubleCoset.doubleCoset _ _ _ = DoubleCoset.doubleCoset _ _ _
      have h_one : (diagMat 2 (fun _ : Fin 2 => 1) : GL (Fin 2) ℚ) = 1 := by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [diagMat, Matrix.diagonal, Matrix.one_apply]
      show DoubleCoset.doubleCoset (diagMat 2 (fun _ : Fin 2 => 1)) _ _ =
           DoubleCoset.doubleCoset 1 _ _
      rw [h_one]
    · obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
      have hp_gcd : Int.gcd (↑p) ↑N = 1 := by
        rw [Int.gcd_natCast_natCast] at hd_gcd ⊢
        exact Nat.Coprime.coprime_dvd_left hp_dvd hd_gcd
      have hp_not_dvd_N : ¬(p ∣ N) := by
        intro h; rw [Int.gcd_natCast_natCast] at hp_gcd
        exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, dvd_refl p, h⟩ hp_gcd
      have h_Tpp : HeckeRing.T_single (Gamma0_pair N) ℤ
          (T_diag_Gamma0 N (![p, p]) (fun i => by fin_cases i <;> simp [hp.pos])
            (by show Int.gcd (↑p) ↑N = 1; exact hp_gcd)) 1 ∈ (ψ_hom N).range :=
        ⟨MvPolynomial.X (⟨p, hp⟩, (1 : Fin 2)), by
          show ψ_hom N (MvPolynomial.X (⟨p, hp⟩, (1 : Fin 2))) = _
          simp only [ψ_hom, MvPolynomial.eval₂Hom_X']
          simp only [show (1 : Fin 2) ≠ 0 from by omega, ↓reduceIte,
            dif_neg hp_not_dvd_N]⟩
      have h_pp_eq : T_diag_Gamma0 N (![p, p])
          (fun i => by fin_cases i <;> simp [hp.pos])
          (by show Int.gcd (↑p) ↑N = 1; exact hp_gcd) =
        T_diag_Gamma0 N (fun _ : Fin 2 => p) (fun _ => hp.pos) hp_gcd := by
        congr 1
        funext i; fin_cases i <;> rfl
      rw [h_pp_eq] at h_Tpp
      set e := d / p with he_def
      have he_pos : 0 < e := by
        rw [he_def]
        exact Nat.div_pos (Nat.le_of_dvd hd hp_dvd) hp.pos
      have he_mul : d = p * e := (Nat.mul_div_cancel' hp_dvd).symm
      have he_lt : e < d := by
        rw [he_mul]; exact lt_mul_of_one_lt_left he_pos hp.one_lt
      have he_gcd : Int.gcd (↑e) ↑N = 1 := by
        rw [Int.gcd_natCast_natCast] at hd_gcd ⊢
        refine Nat.Coprime.coprime_dvd_left ?_ hd_gcd
        exact ⟨p, he_mul.trans (mul_comm p e)⟩
      have h_Te := ih e he_lt he_pos he_gcd
      have h_prod := T_Gamma0_scalar_mul_gen N p hp.pos (fun _ : Fin 2 => e)
        (fun _ => he_pos) hp_gcd he_gcd (dvd_refl e)
      -- (fun _ => p) * (fun _ => e) = (fun _ => d)
      have hpe_eq : (fun _ : Fin 2 => p) * (fun _ : Fin 2 => e) = (fun _ : Fin 2 => d) := by
        ext i; simp [Pi.mul_apply, ← he_mul]
      have hD_eq' : T_diag_Gamma0 N ((fun _ : Fin 2 => p) * (fun _ : Fin 2 => e))
          (fun i => Nat.mul_pos hp.pos he_pos)
          (by show Int.gcd (↑(p * e)) ↑N = 1; rw [← he_mul]; exact hd_gcd) =
        T_diag_Gamma0 N (fun _ : Fin 2 => d) (fun _ => hd) hd_gcd := by
        show (⟦⟨diagMat 2 ((fun _ : Fin 2 => p) * (fun _ : Fin 2 => e)), _⟩⟧ : HeckeCoset _) =
             ⟦⟨diagMat 2 (fun _ : Fin 2 => d), _⟩⟧
        congr 1
        apply Subtype.ext
        show diagMat 2 ((fun _ : Fin 2 => p) * (fun _ : Fin 2 => e)) = diagMat 2 _
        rw [hpe_eq]
      rw [hD_eq'] at h_prod
      rw [← h_prod]
      exact (ψ_hom N).range.mul_mem h_Tpp h_Te

/-- **Target surjectivity** (Shimura Thm 3.34): `𝕋 (Gamma0_pair N) ℤ` is generated
    as a ring by the images of `ψ`. -/
private lemma ψ_surjective :
    Function.Surjective (ψ_hom N) := by
  intro y
  induction y using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add f g hf hg =>
    obtain ⟨xf, rfl⟩ := hf; obtain ⟨xg, rfl⟩ := hg
    exact ⟨xf + xg, map_add _ _ _⟩
  | single D c =>
    suffices h : Finsupp.single D 1 ∈ (ψ_hom N).range by
      obtain ⟨x, hx⟩ := h
      refine ⟨c • x, ?_⟩
      rw [map_zsmul, hx]
      show c • Finsupp.single D (1 : ℤ) = Finsupp.single D c
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    obtain ⟨a, ha, hgcd, hdiv, hrep⟩ := Gamma0_exists_diag_rep N (HeckeCoset.rep D)
    have hD : D = T_diag_Gamma0 N a ha hgcd := by
      rw [show D = (⟦HeckeCoset.rep D⟧ : HeckeCoset (Gamma0_pair N)) from
        (Quotient.out_eq D).symm, hrep]
    rw [hD]
    exact T_diag_mem_ψ_range N a ha hgcd hdiv

/-- The surjective ring hom `R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N))` via factorization. -/
private noncomputable def shimura_ring_hom :
    HeckeAlgebra 2 →+* HeckeRing.𝕋 (Gamma0_pair N) ℤ :=
  (Ideal.Quotient.lift (RingHom.ker π_hom) (ψ_hom N)
    (fun a ha => (ker_π_le_ker_ψ N) ha)).comp
    (RingHom.quotientKerEquivOfSurjective π_surjective).symm.toRingHom

/-- `shimura_ring_hom` is surjective. -/
private theorem shimura_ring_hom_surjective :
    Function.Surjective (shimura_ring_hom N) := by
  show Function.Surjective ((Ideal.Quotient.lift (RingHom.ker π_hom) (ψ_hom N)
    (fun a ha => (ker_π_le_ker_ψ N) ha)).comp
    (RingHom.quotientKerEquivOfSurjective π_surjective).symm.toRingHom)
  exact (Ideal.Quotient.lift_surjective_of_surjective (RingHom.ker π_hom)
      (fun a ha => (ker_π_le_ker_ψ N) ha) (ψ_surjective N)).comp
    (RingHom.quotientKerEquivOfSurjective π_surjective).symm.surjective

/-- **Shimura Theorem 3.35**: There exists a surjective ring homomorphism
    `R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N))`. -/
theorem shimura_thm_3_35 (N : ℕ) [NeZero N] :
    ∃ φ : HeckeRing.𝕋 (GL_pair 2) ℤ →+* HeckeRing.𝕋 (Gamma0_pair N) ℤ,
      Function.Surjective φ :=
  ⟨shimura_ring_hom N, shimura_ring_hom_surjective N⟩


end HeckeRing.GLn
