/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Data.Finset.NatDivisors
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.Modularforms.QExpansionSlash

/-!
# Fourier coefficient formula for Hecke operators

States the key Fourier coefficient formulas for the action of Hecke operators
on q-expansions, building on the T_n definitions from `GL2/HeckeT_n.lean`
and Mathlib's q-expansion infrastructure.

## Main results

Period-`N` cascade (original convention; sparse at non-multiples of `N`):

* `fourierCoeff_heckeT_p` — the fundamental prime formula (DS Prop 5.2.2):
    `a_m(T_p f) = p^{1-k} a_{pm}(f) + χ(p) a_{m/p}(f)`
    (in our slash normalisation; DS has `a_{pm} + χ(p) p^{k-1} a_{m/p}`)
* `fourierCoeff_heckeT_n` — the general formula (DS Prop 5.3.1):
    `a_m(T_n f) = Σ_{d | gcd(m,n)} d^{k-1} χ(d) a_{mn/d²}(f)`
* `eigenvalue_eq_fourierCoeff` — for normalised eigenforms (Miy Thm 4.5.16):
    if `f|T_n = λ_n f` and `a_1(f) = 1`, then `λ_n = a_n(f)`

Canonical period-1 cascade (T082; the standard Miyake / Diamond–Shurman
Fourier convention, consumed by `Newforms.lean`):

* `fourierCoeff_heckeT_ppow_period_one`,
  `fourierCoeff_heckeT_n_period_one` — period-1 siblings of the prime-power
  and general `T_n` formulas.
* `IsNormalisedEigenform_one` — period-1 normalised-eigenform predicate
  using `(qExpansion (1 : ℝ) f).coeff 1 = 1`, superseding
  `IsNormalisedEigenform` (whose period-`N` condition is vacuous for
  `N > 1`).
* `eigenvalue_eq_fourierCoeff_one`,
  `eigenform_coeff_multiplicative_one` — period-1 bridges consumed by
  `Newforms.lean` via `Newform.eigenvalue_eq_coeff` and
  `Newform.eigenvalue_coprime_mul`.

## Implementation notes

**Normalisation**: Our slash action omits `det^{k-1}`. Consequently:
- `T_p` in our convention equals `p^{1-k} T_p^{DS}`.
- The Fourier formula picks up `p^{1-k}` on the leading term instead of `p^{k-1}`
  on the second term.

**q-expansion API.**  For `f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k`,
the **canonical Fourier period is `h = 1`** — not `N` — because
`ModularGroup.T ∈ Γ₁(N)`, so every `Γ₁(N)`-form is `1`-periodic.  At
`h = 1`, `(qExpansion (1 : ℝ) f).coeff n` is the standard Fourier
coefficient `a_n`.  A period-`N` q-expansion is also well-defined (every
integer is a strict period of `Γ₁(N)`) but is *sparse*: its coefficient
vanishes at every non-multiple of `N`.  The period-`N` formulas in this
file are retained for historical compatibility; the period-1 variants
(T082) are the convention used downstream in `Newforms.lean` /
`LFunction.lean`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.2 Prop 5.2.2, §5.3 Prop 5.3.1
* [Miy] Miyake, *Modular Forms*, §4.5 Thm 4.5.13, Thm 4.5.16
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
  ModularFormClass

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

noncomputable section

namespace HeckeRing.GL2

variable {N : ℕ}

private theorem gcd_quot_sq_eq {m a b d₁ : ℕ} (hab : Nat.Coprime a b)
    (hd₁m : d₁ ∣ m) (hd₁a : d₁ ∣ a) :
    (m * a / (d₁ * d₁)).gcd b = m.gcd b := by
  rw [Nat.mul_div_mul_comm hd₁m hd₁a,
    Nat.Coprime.gcd_mul_right_cancel (m / d₁) (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hd₁a) hab)]
  conv_rhs => rw [show m = m / d₁ * d₁ from (Nat.div_mul_cancel hd₁m).symm]
  rw [Nat.Coprime.gcd_mul_right_cancel (m / d₁) (Nat.Coprime.coprime_dvd_left hd₁a hab)]

private theorem div_sq_product {m a b d₁ d₂ : ℕ}
    (hd₁ : d₁ * d₁ ∣ m * a) :
    m * (a * b) / (d₁ * d₂ * (d₁ * d₂)) = m * a / (d₁ * d₁) * b / (d₂ * d₂) := by
  rw [show d₁ * d₂ * (d₁ * d₂) = d₁ * d₁ * (d₂ * d₂) by ring]
  rw [show m * (a * b) = m * a * b by ring]
  rw [← Nat.div_div_eq_div_mul]
  congr 1
  exact Nat.mul_div_right_comm hd₁ b

private theorem unitOfCoprime_mul {N d₁ d₂ : ℕ} (h₁ : d₁.Coprime N) (h₂ : d₂.Coprime N)
    (h₁₂ : (d₁ * d₂).Coprime N)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    (↑(χ (ZMod.unitOfCoprime (d₁ * d₂) h₁₂)) : ℂ) =
      ↑(χ (ZMod.unitOfCoprime d₁ h₁)) * ↑(χ (ZMod.unitOfCoprime d₂ h₂)) := by
  have : χ (ZMod.unitOfCoprime (d₁ * d₂) h₁₂) =
      χ (ZMod.unitOfCoprime d₁ h₁) * χ (ZMod.unitOfCoprime d₂ h₂) := by
    rw [← map_mul]
    congr 1
    ext
    simp [ZMod.coe_unitOfCoprime]
  rw [this]; push_cast; ring

private lemma unitOfCoprime_one_eq_one {N : ℕ} :
    ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
  ext; simp [ZMod.coe_unitOfCoprime]

private lemma chi_unitOfCoprime_one_eq_one {N : ℕ} (χ : (ZMod N)ˣ →* ℂˣ)
    (h : Nat.Coprime 1 N) :
    (↑(χ (ZMod.unitOfCoprime 1 h)) : ℂ) = 1 := by
  have : ZMod.unitOfCoprime 1 h = 1 := by ext; simp [ZMod.coe_unitOfCoprime]
  rw [this, map_one, Units.val_one]

private theorem divisorSum_coprime_conv {N : ℕ} [NeZero N]
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (c : ℕ → ℂ) (m a b : ℕ)
    (hab : Nat.Coprime a b) :
    ∑ d ∈ (m.gcd (a * b)).divisors,
      (if h : d.Coprime N then
        (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
          c (m * (a * b) / (d * d))
      else 0) =
    ∑ d₁ ∈ (m.gcd a).divisors,
      (if h₁ : d₁.Coprime N then
        (↑d₁ : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d₁ h₁)) *
          (∑ d₂ ∈ ((m * a / (d₁ * d₁)).gcd b).divisors,
            if h₂ : d₂.Coprime N then
              (↑d₂ : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d₂ h₂)) *
                c (m * a / (d₁ * d₁) * b / (d₂ * d₂))
            else 0)
      else 0) := by
  have h_gcd_inner : ∀ d₁ ∈ (m.gcd a).divisors,
      ((m * a / (d₁ * d₁)).gcd b) = m.gcd b := fun d₁ hd₁ ↦
    gcd_quot_sq_eq hab (dvd_trans (Nat.dvd_of_mem_divisors hd₁) (Nat.gcd_dvd_left m a))
      (dvd_trans (Nat.dvd_of_mem_divisors hd₁) (Nat.gcd_dvd_right m a))
  rw [hab.gcd_mul m]
  rw [Nat.divisors_mul]
  have hprod_inj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1 * p.2)
      (↑((m.gcd a).divisors ×ˢ (m.gcd b).divisors)) := by
    intro ⟨d₁, d₂⟩ hd ⟨e₁, e₂⟩ he hmul
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hd he
    have hd₁a : d₁ ∣ a := dvd_trans (Nat.dvd_of_mem_divisors hd.1) (Nat.gcd_dvd_right m a)
    have hd₂b : d₂ ∣ b := dvd_trans (Nat.dvd_of_mem_divisors hd.2) (Nat.gcd_dvd_right m b)
    have he₁a : e₁ ∣ a := dvd_trans (Nat.dvd_of_mem_divisors he.1) (Nat.gcd_dvd_right m a)
    have he₂b : e₂ ∣ b := dvd_trans (Nat.dvd_of_mem_divisors he.2) (Nat.gcd_dvd_right m b)
    have hd₁e₂ : Nat.Coprime d₁ e₂ :=
      hab.coprime_dvd_left hd₁a |>.coprime_dvd_right he₂b
    have he₁d₂ : Nat.Coprime e₁ d₂ :=
      hab.coprime_dvd_left he₁a |>.coprime_dvd_right hd₂b
    have hmul' : d₁ * d₂ = e₁ * e₂ := hmul
    have h1 : d₁ ∣ e₁ := hd₁e₂.dvd_of_dvd_mul_right (hmul' ▸ dvd_mul_right d₁ d₂)
    have h2 : e₁ ∣ d₁ := he₁d₂.dvd_of_dvd_mul_right (hmul'.symm ▸ dvd_mul_right e₁ e₂)
    have hd₁_pos : 0 < d₁ := Nat.pos_of_mem_divisors hd.1
    have he₁_pos : 0 < e₁ := Nat.pos_of_mem_divisors he.1
    have heq1 : d₁ = e₁ := Nat.le_antisymm (Nat.le_of_dvd he₁_pos h1) (Nat.le_of_dvd hd₁_pos h2)
    exact Prod.ext heq1 (Nat.eq_of_mul_eq_mul_left hd₁_pos (heq1 ▸ hmul'))
  have hmul_eq : (m.gcd a).divisors * (m.gcd b).divisors =
      Finset.image (fun p : ℕ × ℕ ↦ p.1 * p.2) ((m.gcd a).divisors ×ˢ (m.gcd b).divisors) := by
    ext d
    simp only [Finset.mem_mul, Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  rw [hmul_eq, Finset.sum_image (fun a ha b hb h ↦ hprod_inj ha hb h)]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d₁ hd₁
  have hd₁_dvd := Nat.dvd_of_mem_divisors hd₁
  have hd₁m : d₁ ∣ m := dvd_trans hd₁_dvd (Nat.gcd_dvd_left m a)
  have hd₁a : d₁ ∣ a := dvd_trans hd₁_dvd (Nat.gcd_dvd_right m a)
  have hd₁sq : d₁ * d₁ ∣ m * a := Nat.mul_dvd_mul hd₁m hd₁a
  by_cases h₁ : d₁.Coprime N
  · -- d₁ coprime to N
    rw [dif_pos h₁]
    rw [h_gcd_inner d₁ hd₁]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d₂ hd₂
    by_cases h₂ : d₂.Coprime N
    · -- Both coprime
      have h₁₂ : (d₁ * d₂).Coprime N := Nat.Coprime.mul_left h₁ h₂
      rw [dif_pos h₁₂, dif_pos h₂]
      rw [show (↑(d₁ * d₂) : ℂ) = (↑d₁ : ℂ) * ↑d₂ by push_cast; ring]
      rw [mul_zpow]
      rw [div_sq_product hd₁sq]
      have hchi : ∀ (h : (d₁ * d₂).Coprime N),
          (↑(χ (ZMod.unitOfCoprime (d₁ * d₂) h)) : ℂ) =
          ↑(χ (ZMod.unitOfCoprime d₁ h₁)) * ↑(χ (ZMod.unitOfCoprime d₂ h₂)) :=
        fun h ↦ unitOfCoprime_mul h₁ h₂ h χ
      rw [hchi]
      ring
    · -- d₂ not coprime
      have h₁₂ : ¬(d₁ * d₂).Coprime N := fun h ↦
        h₂ (h.coprime_dvd_left (dvd_mul_left d₂ d₁))
      rw [dif_neg h₁₂, dif_neg h₂]; simp
  · -- d₁ not coprime to N
    rw [dif_neg h₁]
    apply Finset.sum_eq_zero
    intro d₂ _
    have h₁₂ : ¬(d₁ * d₂).Coprime N := fun h ↦
      h₁ (h.coprime_dvd_left (dvd_mul_right d₁ d₂))
    simp [h₁₂]

private lemma sum_divisors_ppow_succ {p : ℕ} (hp : Nat.Prime p) (s : ℕ) (f : ℕ → ℂ) :
    ∑ d ∈ (p ^ (s + 1)).divisors, f d = f 1 + ∑ d ∈ (p ^ s).divisors, f (p * d) := by
  rw [Nat.divisors_prime_pow hp, Nat.divisors_prime_pow hp]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
  have step : ∀ i, f (p * p ^ i) = f (p ^ (i + 1)) := fun i ↦ by rw [pow_succ']
  simp_rw [step]
  rw [Finset.sum_range_succ' (fun i ↦ f (p ^ i))]
  simp [pow_zero, add_comm]

private theorem ppow_divisorSum_recurrence [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (χ : (ZMod N)ˣ →* ℂˣ) (r : ℕ) (m : ℕ) (c : ℕ → ℂ) :
    (((∑ d ∈ ((p * m).gcd (p ^ (r + 1))).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              c (p * m * p ^ (r + 1) / (d * d))
          else 0) +
        (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
          (if p ∣ m then
            ∑ d ∈ ((m / p).gcd (p ^ (r + 1))).divisors,
              if h : d.Coprime N then
                (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
                  c (m / p * p ^ (r + 1) / (d * d))
              else 0
          else 0)) -
      (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
        (∑ d ∈ (m.gcd (p ^ r)).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              c (m * p ^ r / (d * d))
          else 0)) =
    ∑ d ∈ (m.gcd (p ^ (r + 2))).divisors,
      if h : d.Coprime N then
        (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
          c (m * p ^ (r + 2) / (d * d))
      else 0 := by
  have gcd_pm : (p * m).gcd (p ^ (r + 1)) = p * m.gcd (p ^ r) := by
    conv_lhs => rw [pow_succ, mul_comm (p ^ r) p]
    exact Nat.gcd_mul_left p m (p ^ r)
  have hcop : ∀ (a v d : ℕ), d ∈ (a.gcd (p ^ v)).divisors → d.Coprime N :=
    fun a v d hd ↦ Nat.Coprime.coprime_dvd_left
      (dvd_trans (Nat.dvd_of_mem_divisors hd) (Nat.gcd_dvd_right _ _)) (hpN.pow_left v)
  have hppow_cop : ∀ j, (p ^ j).Coprime N := fun j ↦ hpN.pow_left j
  have gcd_is_ppow : ∀ (a v : ℕ), ∃ s, a.gcd (p ^ v) = p ^ s := by
    intro a v
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right a (p ^ v))
    exact ⟨k, hk⟩
  have sum_ppow_to_range : ∀ (s : ℕ) (n : ℕ),
      (∑ d ∈ (p ^ s).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) * c (n / (d * d))
        else 0) =
      ∑ j ∈ Finset.range (s + 1),
        (↑(p ^ j) : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime (p ^ j) (hppow_cop j))) *
          c (n / (p ^ j * p ^ j)) := by
    intro s n
    rw [Nat.divisors_prime_pow hp, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
    apply Finset.sum_congr rfl
    intro j _
    rw [dif_pos (hppow_cop j)]
  by_cases hdvd : p ∣ m
  · -- Case p ∣ m: the three sums telescope
    have gcd_m2 : m.gcd (p ^ (r + 2)) = p * (m / p).gcd (p ^ (r + 1)) := by
      conv_lhs => rw [show m = p * (m / p) from (Nat.mul_div_cancel' hdvd).symm,
        show p ^ (r + 2) = p * p ^ (r + 1) by ring]
      exact Nat.gcd_mul_left p (m / p) (p ^ (r + 1))
    obtain ⟨s₁, hs₁⟩ : ∃ s, m.gcd (p ^ r) = p ^ s := gcd_is_ppow m r
    obtain ⟨s₂, hs₂⟩ : ∃ s, (m / p).gcd (p ^ (r + 1)) = p ^ s := gcd_is_ppow (m / p) (r + 1)
    simp only [hdvd, ↓reduceIte]
    rw [gcd_pm, hs₁, gcd_m2, hs₂]
    rw [show p * p ^ s₁ = p ^ (s₁ + 1) from (pow_succ' p s₁).symm,
        show p * p ^ s₂ = p ^ (s₂ + 1) from (pow_succ' p s₂).symm]
    rw [sum_ppow_to_range (s₁ + 1) (p * m * p ^ (r + 1)),
        sum_ppow_to_range s₂ (m / p * p ^ (r + 1)),
        sum_ppow_to_range s₁ (m * p ^ r),
        sum_ppow_to_range (s₂ + 1) (m * p ^ (r + 2))]
    rw [Finset.sum_range_succ'
      (fun j ↦ (↑(p ^ j) : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime (p ^ j) (hppow_cop j))) *
        c (p * m * p ^ (r + 1) / (p ^ j * p ^ j))),
      Finset.sum_range_succ'
      (fun j ↦ (↑(p ^ j) : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime (p ^ j) (hppow_cop j))) *
        c (m * p ^ (r + 2) / (p ^ j * p ^ j)))]
    simp only [pow_zero, Nat.cast_one, one_zpow, one_mul]
    simp only [chi_unitOfCoprime_one_eq_one χ, one_mul, Nat.div_one]
    have h_prod_eq : p * m * p ^ (r + 1) = m * p ^ (r + 2) := by ring
    rw [h_prod_eq]
    have factor_summand : ∀ (j : ℕ) (n : ℕ),
        (↑(p ^ (j + 1)) : ℂ) ^ (k - 1) *
          ↑(χ (ZMod.unitOfCoprime (p ^ (j + 1)) (hppow_cop (j + 1)))) *
          c (n / (p ^ (j + 1) * p ^ (j + 1))) =
        (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
          ((↑(p ^ j) : ℂ) ^ (k - 1) *
           ↑(χ (ZMod.unitOfCoprime (p ^ j) (hppow_cop j))) *
           c (n / (p ^ (j + 1) * p ^ (j + 1)))) := by
      intro j n
      have h_pow : (↑(p ^ (j + 1)) : ℂ) ^ (k - 1) =
          (↑p : ℂ) ^ (k - 1) * (↑(p ^ j) : ℂ) ^ (k - 1) := by
        rw [pow_succ']; push_cast; rw [mul_zpow]
      have h_chi : (↑(χ (ZMod.unitOfCoprime (p ^ (j + 1)) (hppow_cop (j + 1)))) : ℂ) =
          ↑(χ (ZMod.unitOfCoprime p hpN)) *
          ↑(χ (ZMod.unitOfCoprime (p ^ j) (hppow_cop j))) := by
        have : ZMod.unitOfCoprime (p ^ (j + 1)) (hppow_cop (j + 1)) =
            ZMod.unitOfCoprime p hpN * ZMod.unitOfCoprime (p ^ j) (hppow_cop j) := by
          ext; simp [ZMod.coe_unitOfCoprime, pow_succ']
        rw [this, map_mul]; push_cast; ring
      rw [h_pow, h_chi]; ring
    have div_shift : ∀ j,
        m * p ^ (r + 2) / (p ^ (j + 1) * p ^ (j + 1)) = m * p ^ r / (p ^ j * p ^ j) := by
      intro j
      rw [show p ^ (j + 1) * p ^ (j + 1) = p * p * (p ^ j * p ^ j) by ring]
      rw [show m * p ^ (r + 2) = p * p * (m * p ^ r) by ring]
      exact Nat.mul_div_mul_left _ _ (Nat.mul_pos hp.pos hp.pos)
    have h_mp_prod : m / p * p ^ (r + 1) = m * p ^ r := by
      rw [show p ^ (r + 1) = p * p ^ r by ring, ← mul_assoc, Nat.div_mul_cancel hdvd]
    have sum1_factor :
        ∑ j ∈ Finset.range (s₁ + 1),
          (↑(p ^ (j + 1)) : ℂ) ^ (k - 1) *
            ↑(χ (ZMod.unitOfCoprime (p ^ (j + 1)) (hppow_cop (j + 1)))) *
            c (m * p ^ (r + 2) / (p ^ (j + 1) * p ^ (j + 1))) =
        (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
          ∑ j ∈ Finset.range (s₁ + 1),
            (↑(p ^ j) : ℂ) ^ (k - 1) *
              ↑(χ (ZMod.unitOfCoprime (p ^ j) (hppow_cop j))) *
              c (m * p ^ r / (p ^ j * p ^ j)) := by
      conv_lhs => arg 2; ext j; rw [factor_summand j, div_shift]
      exact (Finset.mul_sum _ _ _).symm
    have sum2_factor :
        ∑ j ∈ Finset.range (s₂ + 1),
          (↑(p ^ (j + 1)) : ℂ) ^ (k - 1) *
            ↑(χ (ZMod.unitOfCoprime (p ^ (j + 1)) (hppow_cop (j + 1)))) *
            c (m * p ^ (r + 2) / (p ^ (j + 1) * p ^ (j + 1))) =
        (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
          ∑ j ∈ Finset.range (s₂ + 1),
            (↑(p ^ j) : ℂ) ^ (k - 1) *
              ↑(χ (ZMod.unitOfCoprime (p ^ j) (hppow_cop j))) *
              c (m / p * p ^ (r + 1) / (p ^ j * p ^ j)) := by
      conv_lhs => arg 2; ext j; rw [factor_summand j, div_shift, ← h_mp_prod]
      exact (Finset.mul_sum _ _ _).symm
    rw [sum1_factor, sum2_factor]
    ring
  · -- Case ¬p ∣ m: all gcd(m, p^v) = 1, gcd(p*m, p^{r+1}) = p
    have gcd_m : ∀ v, m.gcd (p ^ v) = 1 :=
      fun v ↦ Nat.Prime.coprime_pow_of_not_dvd hp hdvd
    have gcd_pm_eq : (p * m).gcd (p ^ (r + 1)) = p := by
      rw [gcd_pm, gcd_m r, mul_one]
    simp only [hdvd, ↓reduceIte, mul_zero, add_zero]
    rw [gcd_m (r + 2), Nat.divisors_one, Finset.sum_singleton]
    simp only [Nat.Coprime, Nat.gcd_one_left, dite_true]
    rw [gcd_m r, Nat.divisors_one, Finset.sum_singleton]
    rw [gcd_pm_eq, hp.divisors, Finset.sum_insert (by simp; exact Ne.symm hp.one_lt.ne')]
    simp only [Finset.sum_singleton]
    simp only [Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow, one_mul, Nat.div_one]
    simp only [hpN, dite_true]
    have hp_pos : 0 < p := hp.pos
    have h_div_pp : p * m * p ^ (r + 1) / (p * p) = m * p ^ r := by
      rw [show p * m * p ^ (r + 1) = p * p * (m * p ^ r) by ring]
      exact Nat.mul_div_cancel_left _ (Nat.mul_pos hp_pos hp_pos)
    rw [h_div_pp]
    have h_eq_prod : p * m * p ^ (r + 1) = m * p ^ (r + 2) := by ring
    rw [h_eq_prod]
    simp only [chi_unitOfCoprime_one_eq_one χ, one_mul]
    ring

private theorem heckeT_ppow_preserves_charSpace [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (r : ℕ)
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    heckeT_ppow k p hp r f ∈ modFormCharSpace k χ := by
  rw [mem_modFormCharSpace_iff] at hf ⊢
  intro d
  have : diamondOpHom k d (heckeT_ppow k p hp r f) =
      heckeT_ppow k p hp r (diamondOpHom k d f) :=
    DFunLike.congr_fun (heckeT_ppow_comm_diamondOp k hp hpN r d) f
  rw [this, hf d, map_smul]

private theorem diamondOp_ext_charSpace [NeZero N] (k : ℤ) {p : ℕ}
    (hpN : Nat.Coprime p N)
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    diamondOp_ext k p f = (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) • f := by
  rw [diamondOp_ext_coprime k hpN]
  exact (mem_modFormCharSpace_iff k χ f).mp hf (ZMod.unitOfCoprime p hpN)

private theorem fourierCoeff_heckeT_ppow [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ) (v : ℕ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) (m : ℕ) :
    (qExpansion N (heckeT_ppow k p hp v f)).coeff m =
      ∑ d ∈ (Nat.gcd m (p ^ v)).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion N f).coeff (m * p ^ v / (d * d))
        else 0 := by
  suffices key : ∀ v, ∀ f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k,
      f ∈ modFormCharSpace k χ → ∀ m,
      (qExpansion N (heckeT_ppow k p hp v f)).coeff m =
        ∑ d ∈ (Nat.gcd m (p ^ v)).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              (qExpansion N f).coeff (m * p ^ v / (d * d))
          else 0 from key v f hf m
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih_v =>
  intro f hf m
  match v with
  | 0 =>
    simp only [pow_zero, heckeT_ppow, Module.End.one_apply, Nat.gcd_one_right,
      Nat.divisors_one, Finset.sum_singleton]
    simp only [Nat.Coprime, Nat.gcd_one_left, dite_true]
    simp [unitOfCoprime_one_eq_one]
  | 1 =>
    rw [pow_one, heckeT_ppow_one_eq_heckeT_p k hp hpN,
      fourierCoeff_heckeT_p k hp hpN χ hf m]
    by_cases hdvd : p ∣ m
    · rw [Nat.gcd_eq_right hdvd, hp.divisors, Finset.sum_insert (by simp; exact hp.one_lt.ne)]
      simp only [Finset.sum_singleton]
      simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
        unitOfCoprime_one_eq_one, map_one, Units.val_one, one_mul, Nat.div_one]
      simp only [hpN, dite_true, if_pos hdvd]
      rw [Nat.mul_div_mul_right m p hp.pos, show p * m = m * p from Nat.mul_comm p m]
    · have hgcd : Nat.gcd m p = 1 := by
        rcases hp.eq_one_or_self_of_dvd (Nat.gcd m p) (Nat.gcd_dvd_right m p) with h | h
        · exact h
        · exact absurd (h ▸ Nat.gcd_dvd_left m p) hdvd
      rw [hgcd, Nat.divisors_one, Finset.sum_singleton]
      simp only [Nat.Coprime, Nat.gcd_one_left, dite_true]
      simp only [unitOfCoprime_one_eq_one, map_one, Units.val_one, Nat.cast_one, one_zpow,
        one_mul, Nat.div_one]
      rw [if_neg hdvd, mul_zero, add_zero, show p * m = m * p from Nat.mul_comm p m]
  | r + 2 =>
    have ih1 : ∀ g ∈ modFormCharSpace k χ, ∀ m',
        (qExpansion N (heckeT_ppow k p hp (r + 1) g)).coeff m' =
          ∑ d ∈ (Nat.gcd m' (p ^ (r + 1))).divisors,
            if h : d.Coprime N then
              (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
                (qExpansion N g).coeff (m' * p ^ (r + 1) / (d * d))
            else 0 := fun g hg m' ↦ ih_v (r + 1) (by omega) g hg m'
    have ih0 : ∀ g ∈ modFormCharSpace k χ, ∀ m',
        (qExpansion N (heckeT_ppow k p hp r g)).coeff m' =
          ∑ d ∈ (Nat.gcd m' (p ^ r)).divisors,
            if h : d.Coprime N then
              (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
                (qExpansion N g).coeff (m' * p ^ r / (d * d))
            else 0 := fun g hg m' ↦ ih_v r (by omega) g hg m'
    have h_rec := heckeT_ppow_succ_succ (N := N) k p hp r
    have h_apply : heckeT_ppow k p hp (r + 2) f =
        heckeT_p_all k p hp (heckeT_ppow k p hp (r + 1) f) -
        (↑p : ℂ) ^ (k - 1) • (diamondOp_ext k p (heckeT_ppow k p hp r f)) :=
      DFunLike.congr_fun h_rec f
    have hf1 : heckeT_ppow k p hp (r + 1) f ∈ modFormCharSpace k χ :=
      heckeT_ppow_preserves_charSpace k hp hpN (r + 1) χ hf
    have hf0 : heckeT_ppow k p hp r f ∈ modFormCharSpace k χ :=
      heckeT_ppow_preserves_charSpace k hp hpN r χ hf
    have h_diamond : diamondOp_ext k p (heckeT_ppow k p hp r f) =
        (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) • heckeT_ppow k p hp r f :=
      diamondOp_ext_charSpace k hpN χ hf0
    have h_p_all : heckeT_p_all k p hp = heckeT_p k p hp hpN :=
      heckeT_p_all_coprime k hp hpN
    rw [h_diamond, smul_smul] at h_apply
    rw [h_p_all] at h_apply
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
    have hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
      rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
        strictPeriods_Gamma1]
      exact ⟨(N : ℤ), by simp⟩
    set χp := (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) with hχp_def
    set cpk := (↑p : ℂ) ^ (k - 1) with hcpk_def
    have h_lhs : (qExpansion N (heckeT_ppow k p hp (r + 2) f)).coeff m =
        (qExpansion N (heckeT_p k p hp hpN (heckeT_ppow k p hp (r + 1) f))).coeff m -
        (cpk * χp) *
          (qExpansion N (heckeT_ppow k p hp r f)).coeff m := by
      have h_coe : (⇑(heckeT_ppow k p hp (r + 2) f) : ℍ → ℂ) =
          ⇑(heckeT_p k p hp hpN (heckeT_ppow k p hp (r + 1) f)) -
          ⇑((cpk * χp) • heckeT_ppow k p hp r f : ModularForm _ k) := by
        change (⇑(heckeT_ppow k p hp (r + 2) f) : ℍ → ℂ) = _
        rw [show (⇑((cpk * χp) • heckeT_ppow k p hp r f : ModularForm _ k) : ℍ → ℂ) =
            (cpk * χp) • ⇑(heckeT_ppow k p hp r f) from rfl]
        exact congr_arg (↑· : ModularForm _ k → ℍ → ℂ) h_apply
      rw [show (qExpansion N (heckeT_ppow k p hp (r + 2) f)).coeff m =
          (qExpansion N (heckeT_ppow k p hp (r + 2) f : ModularForm _ k)).coeff m from rfl]
      conv_lhs => rw [show (⇑(heckeT_ppow k p hp (r + 2) f : ModularForm _ k) : ℍ → ℂ) =
          ⇑(heckeT_p k p hp hpN (heckeT_ppow k p hp (r + 1) f)) -
          ⇑((cpk * χp) • heckeT_ppow k p hp r f : ModularForm _ k) from h_coe]
      rw [qExpansion_sub hN_pos hN_period]
      simp only [map_sub]
      congr 1
      rw [show (⇑((cpk * χp) • heckeT_ppow k p hp r f : ModularForm _ k) : ℍ → ℂ) =
          (cpk * χp) • ⇑(heckeT_ppow k p hp r f) from rfl,
        qExpansion_smul hN_pos hN_period, PowerSeries.coeff_smul, smul_eq_mul]
    rw [h_lhs]
    rw [fourierCoeff_heckeT_p k hp hpN χ hf1]
    rw [ih1 f hf (p * m), ih0 f hf m]
    conv_lhs => rw [show (if p ∣ m then (qExpansion ↑N ⇑((heckeT_ppow k p hp (r + 1)) f)).coeff (m / p) else 0) =
        if p ∣ m then ∑ d ∈ ((m / p).gcd (p ^ (r + 1))).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              (qExpansion N f).coeff (m / p * p ^ (r + 1) / (d * d))
          else 0
        else 0 by split_ifs with h <;> [exact ih1 f hf (m / p); rfl]]
    exact ppow_divisorSum_recurrence k hp hpN χ r m
      (fun j ↦ (qExpansion N f).coeff j)

/-- **General Fourier coefficient formula for T_n** (DS Prop 5.3.1, Miy Thm 4.5.13).

For `f ∈ M_k(Γ₁(N), χ)` and positive integer `n` coprime to `N`:

  `a_m(T_n f) = Σ_{d | gcd(m,n)} d^{k-1} · χ(d) · a_{mn/d²}(f)`

This generalises `fourierCoeff_heckeT_p` and is proved by induction on
the prime factorisation of `n`, using the recurrence `T_{p^r}` and
coprime multiplicativity `T_{mn} = T_m T_n`.
-/
theorem fourierCoeff_heckeT_n [NeZero N] (k : ℤ) (n : ℕ) [NeZero n]
    (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) (m : ℕ) :
    (qExpansion N (heckeT_n k n f)).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion N f).coeff (m * n / (d * d))
        else 0 := by
  suffices key : ∀ (n : ℕ) (hn0 : n ≠ 0) (hn : Nat.Coprime n N)
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
      (hf : f ∈ modFormCharSpace k χ) (m : ℕ),
      haveI : NeZero n := ⟨hn0⟩
      (qExpansion N (heckeT_n k n f)).coeff m =
        ∑ d ∈ (Nat.gcd m n).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              (qExpansion N f).coeff (m * n / (d * d))
          else 0 by
    exact key n (NeZero.ne n) hn f hf m
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro hn0 hnN f hf m
  haveI : NeZero n := ⟨hn0⟩
  by_cases hn1 : n = 1
  · -- Base case: n = 1, T_1 = id
    subst hn1
    simp only [heckeT_n_one, Module.End.one_apply, Nat.gcd_one_right, Nat.divisors_one,
      Finset.sum_singleton]
    simp only [Nat.Coprime, Nat.gcd_one_left, dite_true]
    simp [unitOfCoprime_one_eq_one]
  · -- Inductive step: n > 1
    have hn_gt : 1 < n := by omega
    by_cases hn_prime : Nat.Prime n
    · -- n is prime: reduce to fourierCoeff_heckeT_p
      have hpN : Nat.Coprime n N := hnN
      rw [heckeT_n_prime_coprime k hn_prime hpN]
      rw [fourierCoeff_heckeT_p k hn_prime hpN χ hf m]
      by_cases hdvd : n ∣ m
      · -- n | m: divisors of gcd(m,n) = divisors of n = {1, n}
        rw [Nat.gcd_eq_right hdvd, hn_prime.divisors, Finset.sum_insert (by simp; omega)]
        simp only [Finset.sum_singleton]
        simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
          unitOfCoprime_one_eq_one, map_one, Units.val_one, one_mul, Nat.div_one]
        simp only [hpN, dite_true, if_pos hdvd]
        rw [Nat.mul_div_mul_right m n (by omega), show n * m = m * n from Nat.mul_comm n m]
      · -- n ∤ m: divisors of gcd(m,n) = {1}
        have hgcd : Nat.gcd m n = 1 := by
          rcases hn_prime.eq_one_or_self_of_dvd (Nat.gcd m n) (Nat.gcd_dvd_right m n) with h | h
          · exact h
          · exact absurd (h ▸ Nat.gcd_dvd_left m n) hdvd
        rw [hgcd, Nat.divisors_one, Finset.sum_singleton]
        simp only [Nat.Coprime, Nat.gcd_one_left, dite_true]
        simp only [unitOfCoprime_one_eq_one, map_one, Units.val_one, Nat.cast_one, one_zpow,
          one_mul, Nat.div_one]
        rw [if_neg hdvd, mul_zero, add_zero, show n * m = m * n from Nat.mul_comm n m]
    · -- n is composite (not 1, not prime): decompose n = p^v * q via heckeT_n_unfold
      set p := n.minFac with hp_def
      have hp : Nat.Prime p := Nat.minFac_prime (by omega)
      set v := n.factorization p with hv_def
      set q := n / p ^ v with hq_def
      have hv_pos : 0 < v :=
        hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd n)
      have hq_pos : 0 < q :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p))
          (pow_pos hp.pos v)
      have hq_lt : q < n := heckeT_n_unfold_lt n hn_gt
      have hn_eq : n = p ^ v * q := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      haveI : NeZero q := ⟨hq_pos.ne'⟩
      have h_unfold := heckeT_n_unfold (N := N) k n hn_gt
      have hcop : Nat.Coprime (p ^ v) q :=
        (Nat.coprime_ordCompl hp hn0).pow_left v
      by_cases hq1 : q = 1
      · -- Case q = 1: n = p^v with v ≥ 2 (since n is not prime).
        have hn_ppow : n = p ^ v := by rw [hn_eq, hq1, mul_one]
        have hv_ge2 : 2 ≤ v := by
          by_contra h
          push Not at h
          have hv01 : v = 0 ∨ v = 1 := by omega
          rcases hv01 with hv0 | hv1
          · omega  -- contradicts hv_pos
          · rw [hv1, pow_one] at hn_ppow; exact hn_prime (hn_ppow ▸ hp)
        have hpN : Nat.Coprime p N := by
          rw [hn_ppow] at hnN; exact hnN.coprime_dvd_left (dvd_pow_self p (by omega))
        have h_eq : heckeT_n (N := N) k n f = heckeT_ppow k p hp v f := by
          have h1 := DFunLike.congr_fun h_unfold f
          simp only at h1
          rw [h1]
          show (heckeT_ppow k p hp v) ((heckeT_n k q) f) = (heckeT_ppow k p hp v) f
          congr 1
          have : (heckeT_n (N := N) k q : Module.End ℂ _) = 1 := by
            simp only [show q = 1 from hq1]
            exact heckeT_n_one k
          exact DFunLike.congr_fun this f
        rw [show (qExpansion N ((heckeT_n k n) f)) =
            qExpansion N (heckeT_ppow k p hp v f) by rw [h_eq]]
        rw [hn_ppow]
        exact fourierCoeff_heckeT_ppow k hp hpN χ v hf m
      · -- Case q > 1: both p^v < n and q < n, use IH on both factors.
        have hq_gt1 : 1 < q := by omega
        have hpv_lt : p ^ v < n := by
          calc p ^ v < p ^ v * q := by
                exact lt_mul_of_one_lt_right (pow_pos hp.pos v) hq_gt1
            _ = n := hn_eq.symm
        have hpvN : (p ^ v).Coprime N := by
          rw [hn_eq] at hnN
          exact (hnN.coprime_dvd_left (dvd_mul_right (p ^ v) q))
        have hqN : q.Coprime N := by
          rw [hn_eq] at hnN
          exact (hnN.coprime_dvd_left (dvd_mul_left q (p ^ v)))
        haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
        have h_eq_mul : heckeT_n (N := N) k n = heckeT_n k (p ^ v) * heckeT_n k q := by
          rw [h_unfold, heckeT_n_prime_pow k hp v hv_pos]
        have h_apply : heckeT_n k n f = heckeT_n k (p ^ v) (heckeT_n k q f) := by
          rw [h_eq_mul]; rfl
        have hf_q : heckeT_n k q f ∈ modFormCharSpace k χ :=
          heckeT_n_preserves_charSpace k q hqN χ hf
        have ih_pv := ih (p ^ v) hpv_lt (pow_pos hp.pos v).ne' hpvN
          (heckeT_n k q f) hf_q m
        have ih_q := fun m' ↦ ih q hq_lt hq_pos.ne' hqN f hf m'
        rw [h_apply, ih_pv]
        simp_rw [ih_q]
        rw [hn_eq]
        exact (divisorSum_coprime_conv k χ
          (fun j ↦ (qExpansion N f).coeff j) m (p ^ v) q hcop).symm

/-- A modular form is a **common eigenfunction** of all `T_n` with `(n,N) = 1`
if `T_n f = a · f` for some eigenvalue `a ∈ ℂ`. -/
abbrev IsCommonEigenfunction [NeZero N] (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∀ n : ℕ+, Nat.Coprime n.val N →
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    ∃ a : ℂ, heckeT_n k n.val f = a • f

/-- The eigenvalue of a common eigenfunction at `n`. -/
def eigenvalue [NeZero N] (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : IsCommonEigenfunction k f) (n : ℕ+) (hn : Nat.Coprime n.val N) : ℂ :=
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  (hf n hn).choose

/-- The eigenvalue equation: `T_n f = eigenvalue k f hf n hn • f`. -/
theorem eigenvalue_spec [NeZero N] (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : IsCommonEigenfunction k f) (n : ℕ+) (hn : Nat.Coprime n.val N) :
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeT_n k n.val f = eigenvalue k f hf n hn • f :=
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  (hf n hn).choose_spec

/-- A **normalised eigenform** is a common eigenfunction with `a_1(f) = 1`. -/
def IsNormalisedEigenform [NeZero N] (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  IsCommonEigenfunction k f ∧ (qExpansion N f).coeff 1 = 1

/-- **Eigenvalue = Fourier coefficient** (Miyake Thm 4.5.16, DS (5.21)).

If `f` is a normalised eigenform (`a_1 = 1`) in `M_k(Γ₁(N), χ)` and
`(n, N) = 1`, then the eigenvalue of `T_n` equals the n-th Fourier coefficient:
`λ_n = a_n(f)`. -/
theorem eigenvalue_eq_fourierCoeff [NeZero N] (k : ℤ) (n : ℕ+)
    (hn : Nat.Coprime n.val N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf_char : f ∈ modFormCharSpace k χ)
    (hf_eigen : IsNormalisedEigenform k f) :
    eigenvalue k f hf_eigen.1 n hn = (qExpansion N f).coeff n.val := by
  have hne : NeZero n.val := ⟨n.pos.ne'⟩
  have h1 := fourierCoeff_heckeT_n k n.val hn χ hf_char 1
  simp only [Nat.gcd_one_left, Nat.divisors_one, Finset.sum_singleton] at h1
  simp only [Nat.Coprime, Nat.gcd_one_left, dite_true] at h1
  simp only [Nat.cast_one, one_zpow, unitOfCoprime_one_eq_one, map_one, Units.val_one,
    one_mul, Nat.div_one] at h1
  have hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨(N : ℤ), by simp⟩
  have h_lhs : (qExpansion N (heckeT_n k n.val f)).coeff 1 =
      eigenvalue k f hf_eigen.1 n hn := by
    have h_fun : (⇑(heckeT_n k n.val f) : ℍ → ℂ) =
        eigenvalue k f hf_eigen.1 n hn • ⇑f := by
      change ⇑(heckeT_n k n.val f) = ⇑(eigenvalue k f hf_eigen.1 n hn • f : ModularForm _ k)
      exact congr_arg (↑· : ModularForm _ k → ℍ → ℂ) (eigenvalue_spec k f hf_eigen.1 n hn)
    simp only [h_fun, qExpansion_smul (Nat.cast_pos.mpr (Nat.pos_of_neZero N)) hN_period,
      PowerSeries.coeff_smul, smul_eq_mul, hf_eigen.2, mul_one]
  rw [← h1, h_lhs]

/-- The Fourier coefficients of a normalised eigenform in `M_k(N, χ)` satisfy
the **Hecke multiplicativity relations**:

  `a_m · a_n = Σ_{d | gcd(m,n)} d^{k-1} χ(d) a_{mn/d²}`

In particular, `a_m a_n = a_{mn}` when `gcd(m,n) = 1`.

Reference: [Miy] Lemma 4.5.15. -/
theorem eigenform_coeff_multiplicative [NeZero N] (k : ℤ) (m n : ℕ+)
    (hm : Nat.Coprime m.val N) (_ : Nat.Coprime n.val N)
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf_char : f ∈ modFormCharSpace k χ)
    (hf_eigen : IsNormalisedEigenform k f) :
    (qExpansion N f).coeff m.val * (qExpansion N f).coeff n.val =
      ∑ d ∈ (Nat.gcd m.val n.val).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion N f).coeff (m.val * n.val / (d * d))
        else 0 := by
  haveI : NeZero m.val := ⟨m.pos.ne'⟩
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  have h_fourier := fourierCoeff_heckeT_n k m.val hm χ hf_char n.val
  have h_smul : (qExpansion N (heckeT_n k m.val f)).coeff n.val =
      eigenvalue k f hf_eigen.1 m hm * (qExpansion N f).coeff n.val := by
    have hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
      rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
        strictPeriods_Gamma1]
      exact ⟨(N : ℤ), by simp⟩
    rw [show (⇑(heckeT_n k m.val f) : ℍ → ℂ) =
        ⇑(eigenvalue k f hf_eigen.1 m hm • f : ModularForm _ k) from
        congr_arg (↑· : ModularForm _ k → ℍ → ℂ) (eigenvalue_spec k f hf_eigen.1 m hm),
      ModularForm.IsGLPos.coe_smul,
      qExpansion_smul (Nat.cast_pos.mpr (Nat.pos_of_neZero N)) hN_period,
      PowerSeries.coeff_smul, smul_eq_mul]
  rw [← eigenvalue_eq_fourierCoeff k m hm χ hf_char hf_eigen, ← h_smul]
  rw [Nat.gcd_comm, Nat.mul_comm] at h_fourier
  exact h_fourier

private theorem fourierCoeff_heckeT_ppow_period_one [NeZero N] (k : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ) (v : ℕ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) (m : ℕ) :
    (qExpansion (1 : ℝ) (heckeT_ppow k p hp v f)).coeff m =
      ∑ d ∈ (Nat.gcd m (p ^ v)).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion (1 : ℝ) f).coeff (m * p ^ v / (d * d))
        else 0 := by
  suffices key : ∀ v, ∀ f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k,
      f ∈ modFormCharSpace k χ → ∀ m,
      (qExpansion (1 : ℝ) (heckeT_ppow k p hp v f)).coeff m =
        ∑ d ∈ (Nat.gcd m (p ^ v)).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              (qExpansion (1 : ℝ) f).coeff (m * p ^ v / (d * d))
          else 0 from key v f hf m
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih_v =>
  intro f hf m
  match v with
  | 0 =>
    simp only [pow_zero, heckeT_ppow, Module.End.one_apply, Nat.gcd_one_right,
      Nat.divisors_one, Finset.sum_singleton]
    simp only [Nat.Coprime, Nat.gcd_one_left, dite_true]
    simp [unitOfCoprime_one_eq_one]
  | 1 =>
    rw [pow_one, heckeT_ppow_one_eq_heckeT_p k hp hpN,
      fourierCoeff_heckeT_p_period_one k hp hpN χ hf m]
    by_cases hdvd : p ∣ m
    · rw [Nat.gcd_eq_right hdvd, hp.divisors, Finset.sum_insert (by simp; exact hp.one_lt.ne)]
      simp only [Finset.sum_singleton]
      simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
        unitOfCoprime_one_eq_one, map_one, Units.val_one, one_mul, Nat.div_one]
      simp only [hpN, dite_true, if_pos hdvd]
      rw [Nat.mul_div_mul_right m p hp.pos, show p * m = m * p from Nat.mul_comm p m]
    · have hgcd : Nat.gcd m p = 1 := by
        rcases hp.eq_one_or_self_of_dvd (Nat.gcd m p) (Nat.gcd_dvd_right m p) with h | h
        · exact h
        · exact absurd (h ▸ Nat.gcd_dvd_left m p) hdvd
      rw [hgcd, Nat.divisors_one, Finset.sum_singleton]
      simp only [Nat.Coprime, Nat.gcd_one_left, dite_true]
      simp only [unitOfCoprime_one_eq_one, map_one, Units.val_one, Nat.cast_one, one_zpow,
        one_mul, Nat.div_one]
      rw [if_neg hdvd, mul_zero, add_zero, show p * m = m * p from Nat.mul_comm p m]
  | r + 2 =>
    have ih1 : ∀ g ∈ modFormCharSpace k χ, ∀ m',
        (qExpansion (1 : ℝ) (heckeT_ppow k p hp (r + 1) g)).coeff m' =
          ∑ d ∈ (Nat.gcd m' (p ^ (r + 1))).divisors,
            if h : d.Coprime N then
              (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
                (qExpansion (1 : ℝ) g).coeff (m' * p ^ (r + 1) / (d * d))
            else 0 := fun g hg m' ↦ ih_v (r + 1) (by omega) g hg m'
    have ih0 : ∀ g ∈ modFormCharSpace k χ, ∀ m',
        (qExpansion (1 : ℝ) (heckeT_ppow k p hp r g)).coeff m' =
          ∑ d ∈ (Nat.gcd m' (p ^ r)).divisors,
            if h : d.Coprime N then
              (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
                (qExpansion (1 : ℝ) g).coeff (m' * p ^ r / (d * d))
            else 0 := fun g hg m' ↦ ih_v r (by omega) g hg m'
    have h_rec := heckeT_ppow_succ_succ (N := N) k p hp r
    have h_apply : heckeT_ppow k p hp (r + 2) f =
        heckeT_p_all k p hp (heckeT_ppow k p hp (r + 1) f) -
        (↑p : ℂ) ^ (k - 1) • (diamondOp_ext k p (heckeT_ppow k p hp r f)) :=
      DFunLike.congr_fun h_rec f
    have hf1 : heckeT_ppow k p hp (r + 1) f ∈ modFormCharSpace k χ :=
      heckeT_ppow_preserves_charSpace k hp hpN (r + 1) χ hf
    have hf0 : heckeT_ppow k p hp r f ∈ modFormCharSpace k χ :=
      heckeT_ppow_preserves_charSpace k hp hpN r χ hf
    have h_diamond : diamondOp_ext k p (heckeT_ppow k p hp r f) =
        (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) • heckeT_ppow k p hp r f :=
      diamondOp_ext_charSpace k hpN χ hf0
    have h_p_all : heckeT_p_all k p hp = heckeT_p k p hp hpN :=
      heckeT_p_all_coprime k hp hpN
    rw [h_diamond, smul_smul] at h_apply
    rw [h_p_all] at h_apply
    have h1_pos : (0 : ℝ) < 1 := one_pos
    have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
      rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
        strictPeriods_Gamma1]
      exact ⟨1, by simp⟩
    set χp := (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) with hχp_def
    set cpk := (↑p : ℂ) ^ (k - 1) with hcpk_def
    have h_lhs : (qExpansion (1 : ℝ) (heckeT_ppow k p hp (r + 2) f)).coeff m =
        (qExpansion (1 : ℝ) (heckeT_p k p hp hpN (heckeT_ppow k p hp (r + 1) f))).coeff m -
        (cpk * χp) *
          (qExpansion (1 : ℝ) (heckeT_ppow k p hp r f)).coeff m := by
      have h_coe : (⇑(heckeT_ppow k p hp (r + 2) f) : ℍ → ℂ) =
          ⇑(heckeT_p k p hp hpN (heckeT_ppow k p hp (r + 1) f)) -
          ⇑((cpk * χp) • heckeT_ppow k p hp r f : ModularForm _ k) := by
        change (⇑(heckeT_ppow k p hp (r + 2) f) : ℍ → ℂ) = _
        rw [show (⇑((cpk * χp) • heckeT_ppow k p hp r f : ModularForm _ k) : ℍ → ℂ) =
            (cpk * χp) • ⇑(heckeT_ppow k p hp r f) from rfl]
        exact congr_arg (↑· : ModularForm _ k → ℍ → ℂ) h_apply
      rw [show (qExpansion (1 : ℝ) (heckeT_ppow k p hp (r + 2) f)).coeff m =
          (qExpansion (1 : ℝ)
            (heckeT_ppow k p hp (r + 2) f : ModularForm _ k)).coeff m from rfl]
      conv_lhs => rw [show
          (⇑(heckeT_ppow k p hp (r + 2) f : ModularForm _ k) : ℍ → ℂ) =
          ⇑(heckeT_p k p hp hpN (heckeT_ppow k p hp (r + 1) f)) -
          ⇑((cpk * χp) • heckeT_ppow k p hp r f : ModularForm _ k) from h_coe]
      rw [qExpansion_sub h1_pos h1_period]
      simp only [map_sub]
      congr 1
      rw [show (⇑((cpk * χp) • heckeT_ppow k p hp r f : ModularForm _ k) : ℍ → ℂ) =
          (cpk * χp) • ⇑(heckeT_ppow k p hp r f) from rfl,
        qExpansion_smul h1_pos h1_period, PowerSeries.coeff_smul, smul_eq_mul]
    rw [h_lhs]
    rw [fourierCoeff_heckeT_p_period_one k hp hpN χ hf1]
    rw [ih1 f hf (p * m), ih0 f hf m]
    conv_lhs => rw [show (if p ∣ m then
          (qExpansion (1 : ℝ) ⇑((heckeT_ppow k p hp (r + 1)) f)).coeff (m / p) else 0) =
        if p ∣ m then ∑ d ∈ ((m / p).gcd (p ^ (r + 1))).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              (qExpansion (1 : ℝ) f).coeff (m / p * p ^ (r + 1) / (d * d))
          else 0
        else 0 by split_ifs with h <;> [exact ih1 f hf (m / p); rfl]]
    exact ppow_divisorSum_recurrence k hp hpN χ r m
      (fun j ↦ (qExpansion (1 : ℝ) f).coeff j)

/-- **Period-1 general Fourier coefficient formula for `T_n`.**

For `f ∈ M_k(Γ₁(N), χ)` and positive integer `n` coprime to `N`, at the
canonical Fourier period `h = 1`:
```
a_m(T_n f) = Σ_{d | gcd(m, n)} d^{k-1} · χ(d) · a_{mn/d²}(f)
```
Same divisor-sum formula as `fourierCoeff_heckeT_n` but with every `coeff` at period `1`. -/
theorem fourierCoeff_heckeT_n_period_one [NeZero N] (k : ℤ) (n : ℕ) [NeZero n]
    (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) (m : ℕ) :
    (qExpansion (1 : ℝ) (heckeT_n k n f)).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion (1 : ℝ) f).coeff (m * n / (d * d))
        else 0 := by
  suffices key : ∀ (n : ℕ) (hn0 : n ≠ 0) (hn : Nat.Coprime n N)
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
      (hf : f ∈ modFormCharSpace k χ) (m : ℕ),
      haveI : NeZero n := ⟨hn0⟩
      (qExpansion (1 : ℝ) (heckeT_n k n f)).coeff m =
        ∑ d ∈ (Nat.gcd m n).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              (qExpansion (1 : ℝ) f).coeff (m * n / (d * d))
          else 0 by
    exact key n (NeZero.ne n) hn f hf m
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro hn0 hnN f hf m
  haveI : NeZero n := ⟨hn0⟩
  by_cases hn1 : n = 1
  · subst hn1
    simp only [heckeT_n_one, Module.End.one_apply, Nat.gcd_one_right, Nat.divisors_one,
      Finset.sum_singleton]
    simp only [Nat.Coprime, Nat.gcd_one_left, dite_true]
    simp [unitOfCoprime_one_eq_one]
  · have hn_gt : 1 < n := by omega
    by_cases hn_prime : Nat.Prime n
    · have hpN : Nat.Coprime n N := hnN
      rw [heckeT_n_prime_coprime k hn_prime hpN]
      rw [fourierCoeff_heckeT_p_period_one k hn_prime hpN χ hf m]
      by_cases hdvd : n ∣ m
      · have hgcd : Nat.gcd m n = n := Nat.gcd_eq_right hdvd
        rw [hgcd, hn_prime.divisors, Finset.sum_insert (by simp; omega)]
        simp only [Finset.sum_singleton]
        simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
          unitOfCoprime_one_eq_one, map_one, Units.val_one, one_mul, Nat.div_one]
        simp only [hpN, dite_true, if_pos hdvd]
        have hn_pos : 0 < n := by omega
        have h_div : m * n / (n * n) = m / n :=
          Nat.mul_div_mul_right m n hn_pos
        rw [h_div, show n * m = m * n from Nat.mul_comm n m]
      · have hgcd : Nat.gcd m n = 1 := by
          rcases hn_prime.eq_one_or_self_of_dvd (Nat.gcd m n) (Nat.gcd_dvd_right m n) with h | h
          · exact h
          · exact absurd (h ▸ Nat.gcd_dvd_left m n) hdvd
        rw [hgcd, Nat.divisors_one, Finset.sum_singleton]
        simp only [Nat.Coprime, Nat.gcd_one_left, dite_true]
        simp only [unitOfCoprime_one_eq_one, map_one, Units.val_one, Nat.cast_one, one_zpow,
          one_mul, Nat.div_one]
        rw [if_neg hdvd, mul_zero, add_zero, show n * m = m * n from Nat.mul_comm n m]
    · set p := n.minFac with hp_def
      have hp : Nat.Prime p := Nat.minFac_prime (by omega)
      set v := n.factorization p with hv_def
      set q := n / p ^ v with hq_def
      have hv_pos : 0 < v :=
        hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd n)
      have hq_pos : 0 < q :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p))
          (pow_pos hp.pos v)
      have hq_lt : q < n := heckeT_n_unfold_lt n hn_gt
      have hn_eq : n = p ^ v * q := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      haveI : NeZero q := ⟨hq_pos.ne'⟩
      have h_unfold := heckeT_n_unfold (N := N) k n hn_gt
      have hcop : Nat.Coprime (p ^ v) q :=
        (Nat.coprime_ordCompl hp hn0).pow_left v
      by_cases hq1 : q = 1
      · have hn_ppow : n = p ^ v := by rw [hn_eq, hq1, mul_one]
        have hpN : Nat.Coprime p N := by
          rw [hn_ppow] at hnN; exact hnN.coprime_dvd_left (dvd_pow_self p (by omega))
        have h_eq : heckeT_n (N := N) k n f = heckeT_ppow k p hp v f := by
          have h1 := DFunLike.congr_fun h_unfold f
          simp only at h1
          rw [h1]
          show (heckeT_ppow k p hp v) ((heckeT_n k q) f) = (heckeT_ppow k p hp v) f
          congr 1
          have : (heckeT_n (N := N) k q : Module.End ℂ _) = 1 := by
            simp only [show q = 1 from hq1]
            exact heckeT_n_one k
          exact DFunLike.congr_fun this f
        rw [show (qExpansion (1 : ℝ) ((heckeT_n k n) f)) =
            qExpansion (1 : ℝ) (heckeT_ppow k p hp v f) by rw [h_eq]]
        rw [hn_ppow]
        exact fourierCoeff_heckeT_ppow_period_one k hp hpN χ v hf m
      · have hq_gt1 : 1 < q := by omega
        have hpv_lt : p ^ v < n := by
          calc p ^ v < p ^ v * q := by
                exact lt_mul_of_one_lt_right (pow_pos hp.pos v) hq_gt1
            _ = n := hn_eq.symm
        have hpvN : (p ^ v).Coprime N := by
          rw [hn_eq] at hnN
          exact (hnN.coprime_dvd_left (dvd_mul_right (p ^ v) q))
        have hqN : q.Coprime N := by
          rw [hn_eq] at hnN
          exact (hnN.coprime_dvd_left (dvd_mul_left q (p ^ v)))
        haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
        have h_eq_mul : heckeT_n (N := N) k n = heckeT_n k (p ^ v) * heckeT_n k q := by
          rw [h_unfold, heckeT_n_prime_pow k hp v hv_pos]
        have h_apply : heckeT_n k n f = heckeT_n k (p ^ v) (heckeT_n k q f) := by
          rw [h_eq_mul]; rfl
        have hf_q : heckeT_n k q f ∈ modFormCharSpace k χ :=
          heckeT_n_preserves_charSpace k q hqN χ hf
        have ih_pv := ih (p ^ v) hpv_lt (pow_pos hp.pos v).ne' hpvN
          (heckeT_n k q f) hf_q m
        have ih_q := fun m' ↦ ih q hq_lt hq_pos.ne' hqN f hf m'
        rw [h_apply, ih_pv]
        simp_rw [ih_q]
        rw [hn_eq]
        exact (divisorSum_coprime_conv k χ
          (fun j ↦ (qExpansion (1 : ℝ) f).coeff j) m (p ^ v) q hcop).symm

/-- **Period-1 normalised eigenform.**  A common eigenfunction `f` with
canonical Fourier normalisation `a_1 = (qExpansion (1 : ℝ) f).coeff 1 = 1`.

This is the mathematically-correct Miyake / Diamond–Shurman "`a_1 = 1`"
normalisation and supersedes `IsNormalisedEigenform` (which uses the
period-`N` condition `(qExpansion N f).coeff 1 = 1`; vacuous for `N > 1`
because at period `N` a period-`1` form has `coeff 1 = 0`).  The old
predicate is retained for source compatibility but should not be used
for new results. -/
def IsNormalisedEigenform_one [NeZero N] (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  IsCommonEigenfunction k f ∧ (qExpansion (1 : ℝ) f).coeff 1 = 1

/-- **Period-1 eigenvalue = Fourier coefficient.**

If `f` is a period-1 normalised eigenform in `M_k(Γ₁(N), χ)` and
`(n, N) = 1`, then `λ_n = a_n(f)`. Period-1 analog of
`eigenvalue_eq_fourierCoeff`. -/
theorem eigenvalue_eq_fourierCoeff_one [NeZero N] (k : ℤ) (n : ℕ+)
    (hn : Nat.Coprime n.val N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf_char : f ∈ modFormCharSpace k χ)
    (hf_eigen : IsNormalisedEigenform_one k f) :
    eigenvalue k f hf_eigen.1 n hn = (qExpansion (1 : ℝ) f).coeff n.val := by
  have hne : NeZero n.val := ⟨n.pos.ne'⟩
  have h1 := fourierCoeff_heckeT_n_period_one k n.val hn χ hf_char 1
  simp only [Nat.gcd_one_left, Nat.divisors_one, Finset.sum_singleton] at h1
  simp only [Nat.Coprime, Nat.gcd_one_left, dite_true] at h1
  simp only [Nat.cast_one, one_zpow, unitOfCoprime_one_eq_one, map_one, Units.val_one,
    one_mul, Nat.div_one] at h1
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  have h_lhs : (qExpansion (1 : ℝ) (heckeT_n k n.val f)).coeff 1 =
      eigenvalue k f hf_eigen.1 n hn := by
    have h_fun : (⇑(heckeT_n k n.val f) : ℍ → ℂ) =
        eigenvalue k f hf_eigen.1 n hn • ⇑f := by
      change ⇑(heckeT_n k n.val f) = ⇑(eigenvalue k f hf_eigen.1 n hn • f : ModularForm _ k)
      exact congr_arg (↑· : ModularForm _ k → ℍ → ℂ) (eigenvalue_spec k f hf_eigen.1 n hn)
    simp only [h_fun, qExpansion_smul one_pos h1_period, PowerSeries.coeff_smul,
      smul_eq_mul, hf_eigen.2, mul_one]
  rw [← h1, h_lhs]

/-- **Period-1 Hecke multiplicativity relations** for Fourier coefficients of a normalised
eigenform: `a_m · a_n = Σ_{d | gcd(m, n)} d^{k-1} · χ(d) · a_{mn/d²}`. In particular
`a_m · a_n = a_{mn}` when `gcd(m, n) = 1`. Period-1 analog of
`eigenform_coeff_multiplicative`. -/
theorem eigenform_coeff_multiplicative_one [NeZero N] (k : ℤ) (m n : ℕ+)
    (hm : Nat.Coprime m.val N) (_ : Nat.Coprime n.val N)
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf_char : f ∈ modFormCharSpace k χ)
    (hf_eigen : IsNormalisedEigenform_one k f) :
    (qExpansion (1 : ℝ) f).coeff m.val * (qExpansion (1 : ℝ) f).coeff n.val =
      ∑ d ∈ (Nat.gcd m.val n.val).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion (1 : ℝ) f).coeff (m.val * n.val / (d * d))
        else 0 := by
  haveI : NeZero m.val := ⟨m.pos.ne'⟩
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  have h_fourier := fourierCoeff_heckeT_n_period_one k m.val hm χ hf_char n.val
  have h_smul : (qExpansion (1 : ℝ) (heckeT_n k m.val f)).coeff n.val =
      eigenvalue k f hf_eigen.1 m hm * (qExpansion (1 : ℝ) f).coeff n.val := by
    have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
      rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
        strictPeriods_Gamma1]
      exact ⟨1, by simp⟩
    rw [show (⇑(heckeT_n k m.val f) : ℍ → ℂ) =
        ⇑(eigenvalue k f hf_eigen.1 m hm • f : ModularForm _ k) from
        congr_arg (↑· : ModularForm _ k → ℍ → ℂ) (eigenvalue_spec k f hf_eigen.1 m hm),
      ModularForm.IsGLPos.coe_smul, qExpansion_smul one_pos h1_period,
      PowerSeries.coeff_smul, smul_eq_mul]
  rw [← eigenvalue_eq_fourierCoeff_one k m hm χ hf_char hf_eigen, ← h_smul]
  rw [Nat.gcd_comm, Nat.mul_comm] at h_fourier
  exact h_fourier

end HeckeRing.GL2
