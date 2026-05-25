/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.Modularforms.qExpansion_lems
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum

/-!
# Q-expansion coefficients under Hecke operators

Root-of-unity orthogonality and the Fourier coefficient formulas for
Hecke operators on modular forms, at the period-`N` (original) and
period-`1` (canonical Fourier) conventions.

## Main results

Algebraic helpers:
* `rootOfUnity_sum_eq` — `Σ_{b<n} ζ^{kb} = n` if `n ∣ k`, else `0`.
* `qParam_mul_nat`, `qParam_add` — q-parameter identities.

Period-`N` prime `T_p` (original convention; sparse at non-multiples of
`N`):
* `HeckeRing.GL2.fourierCoeff_heckeT_p`
  (DS Prop 5.2.2): `a_m(T_p f) = a_{pm} + χ(p) · p^{k-1} · [p ∣ m] · a_{m/p}`.

Canonical period-`1` prime `T_p` (T078; the Miyake / Diamond–Shurman
convention consumed by the period-`1` cascade in
`FourierHecke.lean`):
* `HeckeRing.GL2.fourierCoeff_heckeT_p_period_one` — same formula as
  the period-`N` variant but with every `coeff` evaluated at the
  canonical Fourier period.

No-diamond prime `T_p` at a level divisible by `p` (T076, consumed by
`Eigenforms/MainLemma.lean` for the Miyake 4.6.5 prime-sieve witness):
* `HeckeRing.GL2.qExpansion_one_heckeT_p_divN_coeff` —
  `a_m(T_p^{divN} f) = a_{pm}(f)` at period `1`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.2 Prop 5.2.2
* [Miy] Miyake, *Modular Forms*, §4.5 Thm 4.5.13 (period-1 Fourier
  convention)
-/

noncomputable section

open Complex Finset

/-! ### Root-of-unity orthogonality -/

/-- **Root-of-unity orthogonality**: for a primitive `n`-th root of unity `ζ`,
`Σ_{b=0}^{n-1} ζ^{kb} = n` if `n ∣ k`, and `= 0` if `n ∤ k`. -/
theorem rootOfUnity_sum_eq {n : ℕ} (_hn : 1 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (k : ℕ) : ∑ b ∈ range n, ζ ^ (k * b) = if n ∣ k then (n : ℂ) else 0 := by
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    simp [pow_mul, hζ.pow_eq_one, one_pow, sum_const, card_range, nsmul_eq_mul]
  · have hζk : ζ ^ k ≠ 1 := fun h => hdvd (hζ.dvd_of_pow_eq_one k h)
    simp_rw [show ∀ b, ζ ^ (k * b) = (ζ ^ k) ^ b from fun b => by rw [← pow_mul]]
    rw [geom_sum_eq hζk]
    have : (ζ ^ k) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    simp [this]

/-- Variant with `b * k` instead of `k * b`. -/
theorem rootOfUnity_sum_eq' {n : ℕ} (hn : 1 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (k : ℕ) : ∑ b ∈ range n, ζ ^ (b * k) = if n ∣ k then (n : ℂ) else 0 := by
  simp_rw [mul_comm _ k]; exact rootOfUnity_sum_eq hn hζ k

/-! ### Q-parameter identities -/

/-- Scaling the argument by `p`: `qParam h (p · z) = (qParam h z) ^ p`.
This is the key identity for computing q-expansions of `f(pτ)`. -/
theorem qParam_mul_nat (h : ℝ) (p : ℕ) (z : ℂ) :
    Function.Periodic.qParam h (↑p * z) = Function.Periodic.qParam h z ^ p := by
  simp only [Function.Periodic.qParam]
  conv_rhs => rw [← exp_nat_mul]
  congr 1; ring

/-- Shifting by `b` multiplies the q-parameter: `qParam h (z + b) = qParam h z · (qParam h b)`.
For integer `b`, this becomes multiplication by a root of unity when `h | b`. -/
theorem qParam_add (h : ℝ) (z w : ℂ) :
    Function.Periodic.qParam h (z + w) =
      Function.Periodic.qParam h z * Function.Periodic.qParam h w := by
  simp only [Function.Periodic.qParam, add_div, mul_add, exp_add]

/-! ### Fourier coefficients of T_p

The Fourier coefficient formula `a_m(T_p f) = p^{1-k} a_{pm} + χ(p) a_{m/p}`
requires two function-level computations:

**Upper-triangular sum**: For `q = e^{2πiτ}` and `ζ_p = e^{2πi/p}`:
```
  Σ_{b<p} f((τ+b)/p)
    = Σ_{b<p} Σ_n a_n ζ_p^{nb} q^{n/p}     [substitution]
    = Σ_n a_n (Σ_b ζ_p^{nb}) q^{n/p}        [exchange sums]
    = Σ_{p|n} p · a_n · q^{n/p}              [orthogonality]
    = p · Σ_m a_{pm} · q^m                   [reindex n = pm]
```
Dividing by `p^k` (from the slash action denom `p^{-k}`):
the m-th coefficient is `p^{1-k} · a_{pm}`.

**Lower/diamond term**: For `f ∈ M_k(N,χ)`:
```
  (⟨p⟩f)(pτ) = χ(p) f(pτ) = χ(p) Σ_n a_n q^{pn}
```
So the m-th coefficient is `χ(p) a_{m/p}` if `p | m`, else `0`.

The full formalization of these computations requires connecting
`hasSum_qExpansion` with pointwise slash-action evaluation and
sum exchange for absolutely convergent series. The key algebraic
ingredient (`rootOfUnity_sum_eq`) is proved above. -/

namespace HeckeRing.GL2

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
  ModularFormClass

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

variable {N : ℕ}

/-- q-expansion periodicity: for `f` with strict period `1` (e.g., `Γ₁(N)` forms),
the coefficient `(qExpansion N f).coeff n = 0` unless `N ∣ n`.

This is because `f(τ+1) = f(τ)` forces `a_n * (exp(2πin/N) - 1) = 0`,
so `a_n = 0` when `N ∤ n`. -/
theorem qExpansion_coeff_eq_zero_of_not_dvd [NeZero N]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k]
    (hN : (N : ℝ) ∈ Γ.strictPeriods) (h1 : (1 : ℝ) ∈ Γ.strictPeriods)
    (f : F) {n : ℕ} (hn : ¬(N : ℕ) ∣ n) :
    (qExpansion (↑N) f).coeff n = 0 := by
  set ζ := Function.Periodic.qParam (↑N) (1 : ℂ) with hζ_def
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
  have hζ_prim : IsPrimitiveRoot ζ N := by -- ζ = exp(2πi/N) is a primitive N-th root
    rw [hζ_def, Function.Periodic.qParam]
    convert Complex.isPrimitiveRoot_exp N (NeZero.ne N) using 1; push_cast; ring
  have hζn_ne : ζ ^ n ≠ 1 := mt (hζ_prim.pow_eq_one_iff_dvd n).mp hn -- ζ^n ≠ 1 since N ∤ n
  -- Σ a_m (q*ζ)^m = f(τ+1) = f(τ) = Σ a_m q^m, so a_m * ζ^m = a_m by uniqueness
  have h_coeff_eq : ∀ m : ℕ, (qExpansion (↑N) f).coeff m * ζ ^ m =
      (qExpansion (↑N) f).coeff m := by
    intro m; suffices ∀ σ : ℍ, HasSum (fun m' => ((qExpansion (↑N) (⇑f)).coeff m' *
        ζ ^ m') • Function.Periodic.qParam (↑N) ↑σ ^ m') (f σ) from
      qExpansion_coeff_unique hN_pos hN this m
    intro σ
    set σ₁ : ℍ := ⟨↑σ + 1, by simp [Complex.add_im]; linarith [σ.im_pos]⟩
    have h_shift := hasSum_qExpansion f hN_pos hN σ₁
    have hq_shift : Function.Periodic.qParam (↑N) ↑σ₁ =
        Function.Periodic.qParam (↑N) ↑σ * ζ := by simp [σ₁, qParam_add, hζ_def]
    have hf_eq : f σ₁ = f σ := by
      have := (SlashInvariantFormClass.periodic_comp_ofComplex f h1) (↑σ : ℂ)
      simp only [Function.comp_apply] at this
      convert this using 1 <;> congr 1 <;> ext : 1
      · exact (UpperHalfPlane.ofComplex_apply_of_im_pos σ₁.im_pos).symm ▸ rfl
      · exact (UpperHalfPlane.ofComplex_apply σ).symm ▸ rfl
    rw [hq_shift, hf_eq] at h_shift; unfold HasSum at h_shift ⊢
    exact h_shift.congr fun s => by congr 1; ext n'; simp [smul_eq_mul, mul_pow]; ring
  -- a_n * ζ^n = a_n with ζ^n ≠ 1 gives a_n * (ζ^n - 1) = 0, hence a_n = 0
  exact (mul_eq_zero.mp (by rw [mul_sub, mul_one, h_coeff_eq n, sub_self])).resolve_right
    (sub_ne_zero.mpr hζn_ne)


/-- Pointwise slash evaluation for `T_p_upper = [[1,b],[0,p]]`:
`(f ∣[k] T_p_upper b)(τ) = p⁻¹ * f((τ+b)/p)`.
Factor: `|det|^{k-1} * denom^{-k} = p^{k-1} * p^{-k} = p^{-1}`. -/
theorem slash_T_p_upper_eval (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (b : ℕ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) τ =
      (↑p : ℂ)⁻¹ * f (⟨(↑τ + ↑b) / ↑p, by
        simp; exact div_pos (by linarith [τ.im_pos])
          (Nat.cast_pos.mpr hp.pos)⟩ : ℍ) := by
  show ((f ∣[k] glMap (T_p_upper p hp.pos b)) τ) = _
  rw [ModularForm.slash_apply]
  have hdet_val : (glMap (T_p_upper p hp.pos b)).det.val = (p : ℝ) := by
    rw [show (glMap (T_p_upper p hp.pos b)).det.val =
      algebraMap ℚ ℝ (T_p_upper p hp.pos b).det.val from
      congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
      GeneralLinearGroup.val_det_apply, T_p_upper_det]; simp
  have hdet_pos : 0 < (glMap (T_p_upper p hp.pos b)).det.val :=
    hdet_val ▸ Nat.cast_pos.mpr hp.pos
  have hσ : UpperHalfPlane.σ (glMap (T_p_upper p hp.pos b)) = RingHom.id ℂ := by
    unfold UpperHalfPlane.σ; simp only [hdet_pos, ↓reduceIte]
  have hdenom : UpperHalfPlane.denom (glMap (T_p_upper p hp.pos b)) ↑τ = ↑p := by
    simp [UpperHalfPlane.denom, glMap, T_p_upper, Matrix.cons_val_one]
  have hmob : (↑(glMap (T_p_upper p hp.pos b) • τ) : ℂ) = (↑τ + ↑b) / ↑p := by
    simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom,
      UpperHalfPlane.σ, hdet_pos, ↓reduceIte, RingHom.id_apply]
    set M := (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ)
    have h00 : M 0 0 = 1 := by simp [M, glMap, T_p_upper]
    have h01 : M 0 1 = b := by simp [M, glMap, T_p_upper]
    have h10 : M 1 0 = 0 := by simp [M, glMap, T_p_upper]
    have h11 : M 1 1 = p := by simp [M, glMap, T_p_upper, Matrix.cons_val_one]
    simp only [h00, h01, h10, h11]; push_cast; ring
  rw [hσ, RingHom.id_apply, hdet_val, abs_of_pos (Nat.cast_pos.mpr hp.pos), hdenom]
  have hp_ne : (↑p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have halg (x : ℂ) : x * (↑p : ℂ) ^ (k - 1) * (↑p : ℂ) ^ (-k) = (↑p : ℂ)⁻¹ * x := by
    rw [mul_assoc, ← zpow_add₀ hp_ne]; simp [show (k - 1 + -k : ℤ) = -1 by omega]; ring
  convert halg (f (glMap (T_p_upper p hp.pos b) • τ)) using 2
  exact congr_arg f (by ext : 1; exact hmob.symm)

/-- Möbius coordinate of the upper-triangular representative:
`(glMap [[1,b],[0,p]] • τ) = (τ + b) / p`, written with `b/p` split off. -/
private theorem coe_smul_T_p_upper (p : ℕ) (hp : 0 < p) (b : ℕ) (τ : ℍ) :
    (↑(glMap (T_p_upper p hp b) • τ) : ℂ) = ↑τ / ↑p + ↑b / ↑p := by
  simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom]
  have hdet_pos : 0 < (glMap (T_p_upper p hp b)).det.val := by
    rw [show (glMap (T_p_upper p hp b)).det.val =
      algebraMap ℚ ℝ (T_p_upper p hp b).det.val from
      congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
      GeneralLinearGroup.val_det_apply, T_p_upper_det]; simp; linarith [hp]
  simp only [UpperHalfPlane.σ, hdet_pos, ↓reduceIte, RingHom.id_apply,
    show (↑(glMap (T_p_upper p hp b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1
      from by simp [glMap, T_p_upper],
    show (↑(glMap (T_p_upper p hp b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = b
      from by simp [glMap, T_p_upper],
    show (↑(glMap (T_p_upper p hp b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0
      from by simp [glMap, T_p_upper],
    show (↑(glMap (T_p_upper p hp b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = p
      from by simp [glMap, T_p_upper, Matrix.cons_val_one]]
  push_cast; ring

/-- `q`-parameter of the upper-triangular Möbius image factors as a power of the
shrunk parameter `qParam h (τ/p)` times a root-of-unity power `qParam h (1/p) ^ (n·b)`. -/
private theorem qParam_smul_T_p_upper_pow (h : ℝ) (p : ℕ) (hp : 0 < p) (b : ℕ)
    (τ : ℍ) (n : ℕ) :
    Function.Periodic.qParam h ↑(glMap (T_p_upper p hp b) • τ) ^ n =
      Function.Periodic.qParam h ((↑τ : ℂ) / ↑p) ^ n *
        Function.Periodic.qParam h (1 / (↑p : ℂ)) ^ (n * b) := by
  conv_lhs => rw [show (↑(glMap (T_p_upper p hp b) • τ) : ℂ) = ↑τ / ↑p + ↑b / ↑p
    from coe_smul_T_p_upper p hp b τ]
  rw [qParam_add, show (↑b : ℂ) / ↑p = ↑b * (1 / ↑p) from by ring, qParam_mul_nat,
    mul_pow, ← pow_mul, mul_comm b n]

/-- The upper-triangular Hecke sum evaluates to `p⁻¹` times the sum of `f` over the
Möbius images `(τ + b)/p`, `b < p`. -/
private theorem heckeT_p_ut_eq_inv_mul_sum (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (f : ℍ → ℂ) (τ : ℍ) :
    heckeT_p_ut k p hp.pos f τ =
      (↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (⟨(↑τ + ↑b) / ↑p, by
        simp; exact div_pos (by linarith [τ.im_pos]) (Nat.cast_pos.mpr hp.pos)⟩ : ℍ) := by
  simp only [heckeT_p_ut, Finset.sum_apply, Finset.mul_sum]
  congr 1; ext b; exact slash_T_p_upper_eval k p hp b f τ

/-- The lower (diagonal) representative slashes a function `g` to `p^{k-1} · g(pτ)`:
the `|det|^{k-1}` factor with trivial denominator and Möbius image `pτ`. -/
private theorem slash_T_p_lower_eval (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (g : ℍ → ℂ) (τ : ℍ) (pτ : ℍ) (hpτ : (↑pτ : ℂ) = ↑p * ↑τ) :
    (g ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ)) τ = (↑p : ℂ) ^ (k - 1) * g pτ := by
  show (g ∣[k] glMap (T_p_lower p hp.pos)) τ = (↑p : ℂ) ^ (k - 1) * g pτ
  rw [ModularForm.slash_apply]
  have hdet_val : (glMap (T_p_lower p hp.pos)).det.val = (p : ℝ) := by
    rw [show (glMap (T_p_lower p hp.pos)).det.val =
      algebraMap ℚ ℝ (T_p_lower p hp.pos).det.val from
      congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
      GeneralLinearGroup.val_det_apply, T_p_lower_det]; simp
  have hdet_pos : 0 < (glMap (T_p_lower p hp.pos)).det.val := by
    rw [hdet_val]; exact Nat.cast_pos.mpr hp.pos
  have hσ : UpperHalfPlane.σ (glMap (T_p_lower p hp.pos)) = RingHom.id ℂ := by
    unfold UpperHalfPlane.σ; simp only [hdet_pos, ↓reduceIte]
  have hmob : glMap (T_p_lower p hp.pos) • τ = pτ := by
    ext : 1; rw [hpτ]; show (↑(glMap (T_p_lower p hp.pos) • τ) : ℂ) = ↑p * ↑τ
    simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom,
      UpperHalfPlane.σ, hdet_pos, ↓reduceIte, RingHom.id_apply,
      show (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = p
        from by simp [glMap, T_p_lower],
      show (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0
        from by simp [glMap, T_p_lower],
      show (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0
        from by simp [glMap, T_p_lower],
      show (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1
        from by simp [glMap, T_p_lower, Matrix.cons_val_one]]
    push_cast; ring
  have hdenom : UpperHalfPlane.denom (glMap (T_p_lower p hp.pos)) ↑τ = 1 := by
    simp [UpperHalfPlane.denom, glMap, T_p_lower, Matrix.cons_val_one]
  rw [hσ, RingHom.id_apply, hmob, hdenom, one_zpow, mul_one,
    hdet_val, abs_of_pos (Nat.cast_pos.mpr hp.pos)]
  push_cast; ring

/-- Sum-value matching: `f` at the Möbius image of the upper-triangular
representative equals `f` at the explicit point `(τ + b)/p`. -/
private theorem f_smul_T_p_upper_eq (p : ℕ) (hp : Nat.Prime p) (f : ℍ → ℂ)
    (b : ℕ) (τ : ℍ) :
    f (glMap (T_p_upper p hp.pos b) • τ) =
      f (⟨(↑τ + ↑b) / ↑p, by
        simp; exact div_pos (by linarith [τ.im_pos]) (Nat.cast_pos.mpr hp.pos)⟩ : ℍ) := by
  congr 1; ext : 1; rw [coe_smul_T_p_upper p hp.pos b τ]; push_cast; ring

/-- **Root-of-unity orthogonality over the `b`-sum at period `N`.**
For `ζ = qParam N (1/p)` (a primitive `(p·N)`-th root of unity) and any `n`
divisible by `N`, the character sum `Σ_{b<p} ζ^{nb}` collapses to `p` when
`p ∣ n` and to `0` otherwise. -/
private theorem sum_qParam_pow_period_N {N : ℕ} [NeZero N] {p : ℕ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N) {n : ℕ} (hNn : (N : ℕ) ∣ n) :
    ∑ b ∈ Finset.range p, Function.Periodic.qParam (↑N) (1 / (↑p : ℂ)) ^ (n * b) =
      if p ∣ n then (↑p : ℂ) else 0 := by
  set ζ := Function.Periodic.qParam (↑N) (1 / (↑p : ℂ)) with hζ_def
  have hζ_pN : IsPrimitiveRoot ζ (p * N) := by
    rw [hζ_def, Function.Periodic.qParam]
    convert Complex.isPrimitiveRoot_exp (p * N)
      (Nat.mul_ne_zero hp.ne_zero (NeZero.ne N)) using 1
    push_cast; ring
  split_ifs with hpn
  · have hζ_pow : ζ ^ n = 1 :=
      (hζ_pN.pow_eq_one_iff_dvd n).mpr (Nat.Coprime.mul_dvd_of_dvd_of_dvd hpN hpn hNn)
    simp_rw [pow_mul ζ n, hζ_pow, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  · have hζn_ne : ζ ^ n ≠ 1 := by
      intro h_eq
      have hdvd := (hζ_pN.pow_eq_one_iff_dvd n).mp h_eq
      obtain ⟨j, rfl⟩ := hNn
      exact hpn ((Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_neZero N)
        (by rwa [show p * N = N * p from by ring] at hdvd)).mul_left N)
    simp_rw [pow_mul ζ n]
    rw [geom_sum_eq hζn_ne, show (ζ ^ n) ^ p = 1 from by
      obtain ⟨j, rfl⟩ := hNn
      rw [← pow_mul, hζ_pN.pow_eq_one_iff_dvd]; exact ⟨j, by ring⟩]
    simp

/-- **Root-of-unity orthogonality over the `b`-sum at period `1`.**
At the canonical period, `ζ = qParam 1 (1/p)` is a primitive `p`-th root of
unity, so `Σ_{b<p} ζ^{nb}` collapses to `p` when `p ∣ n` and to `0` otherwise,
with no divisibility hypothesis on `n`. -/
private theorem sum_qParam_pow_period_one {p : ℕ} (hp : Nat.Prime p) (n : ℕ) :
    ∑ b ∈ Finset.range p, Function.Periodic.qParam (1 : ℝ) (1 / (↑p : ℂ)) ^ (n * b) =
      if p ∣ n then (↑p : ℂ) else 0 := by
  set ζ := Function.Periodic.qParam (1 : ℝ) (1 / (↑p : ℂ)) with hζ_def
  have hζ_prim : IsPrimitiveRoot ζ p := by
    rw [hζ_def, Function.Periodic.qParam]
    convert Complex.isPrimitiveRoot_exp p hp.ne_zero using 1; push_cast; ring
  split_ifs with hpn
  · simp_rw [pow_mul ζ n, (hζ_prim.pow_eq_one_iff_dvd n).mpr hpn, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · have hζn_ne : ζ ^ n ≠ 1 := mt (hζ_prim.pow_eq_one_iff_dvd n).mp hpn
    simp_rw [pow_mul ζ n]
    rw [geom_sum_eq hζn_ne, show (ζ ^ n) ^ p = 1 from by
      rw [← pow_mul, mul_comm, pow_mul, hζ_prim.pow_eq_one, one_pow]]
    simp

/-- **Upper-triangular HasSum at period `N`.**
The upper-triangular Hecke sum has the `q`-expansion whose `n`-th coefficient is
`a (p·n)`, given that `a` vanishes off multiples of `N` (the `Γ₁(N)`-periodicity
constraint). This is the orthogonality core of the `T_p` Fourier formula. -/
private theorem hasSum_heckeT_p_ut_period_N {N : ℕ} [NeZero N] (k : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (f : ℍ → ℂ) (a : ℕ → ℂ) (τ : ℍ)
    (hf_hs : ∀ σ : ℍ, HasSum
      (fun n => a n • Function.Periodic.qParam (↑N) ↑σ ^ n) (f σ))
    (ha_zero : ∀ n, ¬ (N : ℕ) ∣ n → a n = 0) :
    HasSum (fun n => a (p * n) • Function.Periodic.qParam (↑N) ↑τ ^ n)
      (heckeT_p_ut k p hp.pos f τ) := by
  set q := Function.Periodic.qParam (↑N) ↑τ with hq_def
  rw [heckeT_p_ut_eq_inv_mul_sum k p hp f τ]
  have hinj : Function.Injective (p * · : ℕ → ℕ) := mul_right_injective₀ hp.ne_zero
  set w := Function.Periodic.qParam (↑N) ((↑τ : ℂ) / ↑p) with hw_def
  set ζ := Function.Periodic.qParam (↑N) (1 / (↑p : ℂ)) with hζ_def
  have hp_ne : (↑p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hw_pow_p : w ^ p = q := by rw [hw_def, ← qParam_mul_nat]; congr 1; field_simp
  -- Finite-infinite exchange, then factor each `qParam` via the root-of-unity power.
  have h_rewritten : HasSum
      (fun n => a n • w ^ n * ∑ b ∈ Finset.range p, ζ ^ (n * b))
      (∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ)) := by
    convert hasSum_sum (fun b _ => hf_hs (glMap (T_p_upper p hp.pos b) • τ)) using 2 with n
    trans (∑ b ∈ Finset.range p, a n * (w ^ n * ζ ^ (n * b)))
    · rw [smul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
    · exact Finset.sum_congr rfl fun b _ => by
        rw [qParam_smul_T_p_upper_pow (↑N) p hp.pos b τ n, smul_eq_mul]
  -- Orthogonality collapses the inner sum to the `p ∣ n` indicator.
  have h_ind : HasSum (fun n' => (if p ∣ n' then a n' • w ^ n' else 0))
      ((↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ)) := by
    rw [show (↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ) =
        (↑p : ℂ)⁻¹ • ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ) from by
      simp [smul_eq_mul]]
    have h_scaled := h_rewritten.const_smul (↑p : ℂ)⁻¹
    unfold HasSum at h_scaled ⊢
    refine h_scaled.congr fun s => ?_
    congr 1; ext n
    simp only [smul_eq_mul]
    by_cases ha : a n = 0
    · simp [ha]
    · rw [sum_qParam_pow_period_N hp hpN (not_imp_comm.mp (ha_zero n) ha)]
      split_ifs with h
      · rw [mul_comm (a n * w ^ n), ← mul_assoc, inv_mul_cancel₀ hp_ne, one_mul]
      · ring
  -- Reindex `n ↦ p·n` to drop the indicator, then match powers and sum values.
  rw [← hinj.hasSum_iff (fun x hx => by
    simp only [Set.mem_range, not_exists] at hx
    simp [show ¬p ∣ x from fun ⟨k, hk⟩ => hx k (by omega)])] at h_ind
  simp only [Function.comp_def, show ∀ m, p ∣ p * m from dvd_mul_right p, if_true] at h_ind
  convert h_ind using 2 with m
  · rw [smul_eq_mul, smul_eq_mul, pow_mul, hw_pow_p]
  · exact Finset.sum_congr rfl fun b _ => (f_smul_T_p_upper_eq p hp f b τ).symm

/-- **Upper-triangular HasSum at period `1`.**
Period-`1` sibling of `hasSum_heckeT_p_ut_period_N`: at the canonical period,
`ζ = qParam 1 (1/p)` is a primitive `p`-th root, so the orthogonality is direct
and needs no vanishing hypothesis on the coefficients. Shared by the period-`1`
`T_p` Fourier formula and its no-diamond (`p ∣ M`) specialisation. -/
private theorem hasSum_heckeT_p_ut_period_one (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (f : ℍ → ℂ) (a : ℕ → ℂ) (τ : ℍ)
    (hf_hs : ∀ σ : ℍ, HasSum
      (fun n => a n • Function.Periodic.qParam (1 : ℝ) ↑σ ^ n) (f σ)) :
    HasSum (fun n => a (p * n) • Function.Periodic.qParam (1 : ℝ) ↑τ ^ n)
      (heckeT_p_ut k p hp.pos f τ) := by
  set q := Function.Periodic.qParam (1 : ℝ) ↑τ with hq_def
  rw [heckeT_p_ut_eq_inv_mul_sum k p hp f τ]
  have hinj : Function.Injective (p * · : ℕ → ℕ) := mul_right_injective₀ hp.ne_zero
  set w := Function.Periodic.qParam (1 : ℝ) ((↑τ : ℂ) / ↑p) with hw_def
  set ζ := Function.Periodic.qParam (1 : ℝ) (1 / (↑p : ℂ)) with hζ_def
  have hp_ne : (↑p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hw_pow_p : w ^ p = q := by rw [hw_def, ← qParam_mul_nat]; congr 1; field_simp
  -- Finite-infinite exchange, then factor each `qParam` via the root-of-unity power.
  have h_rewritten : HasSum
      (fun n => a n • w ^ n * ∑ b ∈ Finset.range p, ζ ^ (n * b))
      (∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ)) := by
    convert hasSum_sum (fun b _ => hf_hs (glMap (T_p_upper p hp.pos b) • τ)) using 2 with n
    trans (∑ b ∈ Finset.range p, a n * (w ^ n * ζ ^ (n * b)))
    · rw [smul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
    · exact Finset.sum_congr rfl fun b _ => by
        rw [qParam_smul_T_p_upper_pow (1 : ℝ) p hp.pos b τ n, smul_eq_mul]
  -- `ζ` is a primitive `p`-th root, so orthogonality is unconditional.
  have h_ind : HasSum (fun n' => (if p ∣ n' then a n' • w ^ n' else 0))
      ((↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ)) := by
    rw [show (↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ) =
        (↑p : ℂ)⁻¹ • ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ) from by
      simp [smul_eq_mul]]
    have h_scaled := h_rewritten.const_smul (↑p : ℂ)⁻¹
    unfold HasSum at h_scaled ⊢
    refine h_scaled.congr fun s => ?_
    congr 1; ext n
    simp only [smul_eq_mul]
    rw [sum_qParam_pow_period_one hp n]
    split_ifs with h
    · rw [mul_comm (a n * w ^ n), ← mul_assoc, inv_mul_cancel₀ hp_ne, one_mul]
    · ring
  rw [← hinj.hasSum_iff (fun x hx => by
    simp only [Set.mem_range, not_exists] at hx
    simp [show ¬p ∣ x from fun ⟨k, hk⟩ => hx k (by omega)])] at h_ind
  simp only [Function.comp_def, show ∀ m, p ∣ p * m from dvd_mul_right p, if_true] at h_ind
  convert h_ind using 2 with m
  · rw [smul_eq_mul, smul_eq_mul, pow_mul, hw_pow_p]
  · exact Finset.sum_congr rfl fun b _ => (f_smul_T_p_upper_eq p hp f b τ).symm

/-- **Diamond-side assembly of the `T_p` Fourier formula** (period-generic).
Given the upper-triangular `HasSum` `h_upper`, the diamond eigenvalue `⟨p⟩f = χ(p)f`
adds the lower term: `(T_p f)(τ)` has the `q`-expansion whose `n`-th coefficient is
`a(pn) + p^{k-1}·χ(p)·[p ∣ n]·a(n/p)`. The lower term comes from reindexing
`f(pτ)`'s expansion and slashing through `T_p_lower`. -/
private theorem hasSum_heckeT_p_of_ut {N : ℕ} [NeZero N] (k : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ)
    (h : ℝ) (a : ℕ → ℂ) (τ : ℍ)
    (hf_hs : ∀ σ : ℍ, HasSum (fun n => a n • Function.Periodic.qParam h ↑σ ^ n) (f σ))
    (h_upper : HasSum (fun n => a (p * n) • Function.Periodic.qParam h ↑τ ^ n)
      (heckeT_p_ut k p hp.pos (⇑f) τ)) :
    HasSum (fun n : ℕ => ((a (p * n) + (↑p : ℂ) ^ (k - 1) *
        ↑(χ (ZMod.unitOfCoprime p hpN)) * if p ∣ n then a (n / p) else 0)) •
      Function.Periodic.qParam h ↑τ ^ n) ((heckeT_p k p hp hpN f) τ) := by
  set q := Function.Periodic.qParam h ↑τ with hq_def
  set χp := (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) with hχp_def
  set pk := (↑p : ℂ) ^ (k - 1) with hpk_def
  have hpτ_im : 0 < ((p : ℂ) * ↑τ).im := by
    simp [Complex.mul_im]; exact mul_pos (Nat.cast_pos.mpr hp.pos) τ.im_pos
  set pτ : ℍ := ⟨(p : ℂ) * ↑τ, hpτ_im⟩
  have hinj : Function.Injective (p * · : ℕ → ℕ) := mul_right_injective₀ hp.ne_zero
  -- Lower/diamond term: reindex `f(pτ)`'s expansion to a `p ∣ m` indicator sum.
  have h_lower_ind : HasSum
      (fun m => (if p ∣ m then a (m / p) else 0) • q ^ m) (f pτ) := by
    refine (hinj.hasSum_iff (fun x hx => ?_)).mp ?_
    · simp only [Set.mem_range, not_exists] at hx
      simp [show ¬(p ∣ x) from fun ⟨k, hk⟩ => hx k (by omega)]
    · show HasSum ((fun m => (if p ∣ m then a (m / p) else 0) • q ^ m) ∘ (p * ·)) (f pτ)
      simp only [Function.comp_def, show ∀ n, p ∣ p * n from dvd_mul_right p,
        if_true, Nat.mul_div_cancel_left _ hp.pos]
      have := hf_hs pτ; simp only [pτ, qParam_mul_nat] at this
      convert this using 2 with n; rw [← pow_mul]
  have h_diamond : ∀ σ : ℍ, (diamondOp k (ZMod.unitOfCoprime p hpN) f) σ = χp • f σ := by
    intro σ
    have hd := (mem_modFormCharSpace_iff k χ f).mp hf (ZMod.unitOfCoprime p hpN)
    change (diamondOpHom k (ZMod.unitOfCoprime p hpN) f) σ = χp • f σ
    rw [hd]; rfl
  have h_slash_lower : (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) τ = pk * χp * f pτ := by
    rw [slash_T_p_lower_eval k p hp _ τ pτ rfl, h_diamond pτ, smul_eq_mul]; ring
  have h_lower_scaled : HasSum
      (fun m => (pk * χp * if p ∣ m then a (m / p) else 0) • q ^ m) (pk * χp * f pτ) := by
    have := h_lower_ind.const_smul (pk * χp)
    simp only [smul_eq_mul] at this ⊢
    convert this using 2 with m; split_ifs <;> ring
  convert h_upper.add h_lower_scaled using 1
  · ext n; simp only [smul_eq_mul]; split_ifs <;> ring
  · show heckeT_p_fun k p hp hpN f τ = heckeT_p_ut k p hp.pos (⇑f) τ + pk * χp * f pτ
    simp only [heckeT_p_fun, Pi.add_apply, h_slash_lower]

/-- **Fourier coefficient formula for T_p** (Diamond–Shurman Prop 5.2.2).

For `f ∈ M_k(Γ₁(N), χ)` and prime `p` coprime to `N`:

  `a_m(T_p f) = p^{1-k} · a_{pm}(f) + χ(p) · a_{m/p}(f)`

where `a_{m/p} = 0` when `p ∤ m`.

The proof uses:
1. `rootOfUnity_sum_eq` for the upper-triangular sum (kills non-multiples of p)
2. Diamond eigenvalue `⟨p⟩f = χ(p) f` for the lower term
3. `qExpansion_coeff_unique` for coefficient identification

Mathlib's slash action includes the `|det|^{k-1}` factor, so this matches the
standard Diamond–Shurman normalisation. -/
theorem fourierCoeff_heckeT_p [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) (m : ℕ) :
    (qExpansion N (heckeT_p k p hp hpN f)).coeff m =
      (qExpansion N f).coeff (p * m) +
        (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
          (if p ∣ m then (qExpansion N f).coeff (m / p) else 0) := by
  /- **Proof outline** (`qExpansion_coeff_unique`): for each `τ`, the candidate
  coefficients give a `HasSum` of `(T_p f)(τ)`. The upper-triangular part is
  `hasSum_heckeT_p_ut_period_N` (root-of-unity orthogonality, using that `Γ₁(N)`
  coefficients vanish off multiples of `N`); the diamond/lower assembly is
  `hasSum_heckeT_p_of_ut`. -/
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
  have hΓ : (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) := rfl
  have hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [hΓ, strictPeriods_Gamma1]; exact ⟨(N : ℤ), by simp⟩
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [hΓ, strictPeriods_Gamma1]; exact ⟨1, by simp⟩
  set a := fun n => (qExpansion (↑N) (⇑f)).coeff n with ha_def
  have hf_hs : ∀ σ : ℍ, HasSum (fun n => a n • (Function.Periodic.qParam (↑N) ↑σ) ^ n)
      (f σ) := hasSum_qExpansion f hN_pos hN_period
  suffices key : ∀ τ : ℍ, HasSum
      (fun n : ℕ ↦ (a (p * n) + (↑p : ℂ) ^ (k - 1) *
          ↑(χ (ZMod.unitOfCoprime p hpN)) * if p ∣ n then a (n / p) else 0) •
        Function.Periodic.qParam (↑N) ↑τ ^ n) ((heckeT_p k p hp hpN f) τ) by
    exact (qExpansion_coeff_unique hN_pos hN_period key m).symm
  exact fun τ => hasSum_heckeT_p_of_ut k hp hpN χ hf (↑N) a τ hf_hs
    (hasSum_heckeT_p_ut_period_N k hp hpN (⇑f) a τ hf_hs
      (fun n hn => qExpansion_coeff_eq_zero_of_not_dvd hN_period h1_period f hn))

/-- **Fourier coefficient formula for `T_p` at period 1** (Diamond–Shurman
Prop 5.2.2, canonical period).

Period-1 sibling of `fourierCoeff_heckeT_p`.  Because
`ModularGroup.T ∈ Γ₁(N)`, every `Γ₁(N)`-form is `1`-periodic, and the
canonical `q`-expansion of `f ∈ M_k(Γ₁(N), χ)` uses period `1`.  The
Fourier formula at this canonical period is

  `a_m(T_p f) = a_{pm}(f) + p^{k-1} · χ(p) · a_{m/p}(f)   [if p ∣ m, else 0]`

where `a_m = (qExpansion 1 f).coeff m` are the standard Fourier
coefficients.

Proof structure mirrors `fourierCoeff_heckeT_p` with period `(↑N : ℝ)`
replaced by `(1 : ℝ)` throughout.  The only real simplification: at
period `1`, `ζ := qParam 1 (1/p)` is a primitive **p-th** root of unity
(not the primitive `(p·N)`-th root that appears at period `N`), so the
case analysis in the root-of-unity orthogonality step becomes direct
and does not require `qExpansion_coeff_eq_zero_of_not_dvd`.

Consumed by the period-1 migration of `FourierHecke.lean`
(`fourierCoeff_heckeT_ppow_period_one`, `fourierCoeff_heckeT_n_period_one`)
and ultimately by `Newforms.lean`'s period-1 `Newform.lCoeff` / `isNorm`
convention. -/
theorem fourierCoeff_heckeT_p_period_one [NeZero N] (k : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) (m : ℕ) :
    (qExpansion (1 : ℝ) (heckeT_p k p hp hpN f)).coeff m =
      (qExpansion (1 : ℝ) f).coeff (p * m) +
        (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
          (if p ∣ m then (qExpansion (1 : ℝ) f).coeff (m / p) else 0) := by
  -- Period-`1` analogue of `fourierCoeff_heckeT_p`: upper-triangular part from
  -- `hasSum_heckeT_p_ut_period_one` (primitive `p`-th root, no `N`-vanishing
  -- hypothesis), diamond/lower assembly from `hasSum_heckeT_p_of_ut`.
  have h1_pos : (0 : ℝ) < 1 := one_pos
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  set a := fun n => (qExpansion (1 : ℝ) (⇑f)).coeff n with ha_def
  have hf_hs : ∀ σ : ℍ, HasSum (fun n => a n • (Function.Periodic.qParam (1 : ℝ) ↑σ) ^ n)
      (f σ) := hasSum_qExpansion f h1_pos h1_period
  suffices key : ∀ τ : ℍ, HasSum
      (fun n : ℕ ↦ (a (p * n) + (↑p : ℂ) ^ (k - 1) *
          ↑(χ (ZMod.unitOfCoprime p hpN)) * if p ∣ n then a (n / p) else 0) •
        Function.Periodic.qParam (1 : ℝ) ↑τ ^ n) ((heckeT_p k p hp hpN f) τ) by
    exact (qExpansion_coeff_unique h1_pos h1_period key m).symm
  exact fun τ => hasSum_heckeT_p_of_ut k hp hpN χ hf (1 : ℝ) a τ hf_hs
    (hasSum_heckeT_p_ut_period_one k hp (⇑f) a τ hf_hs)

/-- **Fourier coefficient formula for `T_p` on forms with `p ∣ M` at period 1**
(Diamond–Shurman §5.2, no-diamond case).

For `f ∈ M_k(Γ₁(M))` and prime `p` dividing `M`, the level-divisible Hecke
operator `heckeT_p_divN` is the purely upper-triangular sum
`Σ_{b=0}^{p-1} f ∣[k] [[1,b],[0,p]]` (no lower/diamond term, since the
Nebentypus character is not well-defined at `p`).  At period `1`, its
`m`-th Fourier coefficient collapses to `a_{pm}(f)`:

  `a_m(T_p^{divN} f) = a_{pm}(f)`

This is the "no-diamond" case of the `T_p` Fourier formula at period `1`.
The proof is the upper-triangular / root-of-unity orthogonality argument
from `fourierCoeff_heckeT_p_period_one` specialised by dropping the
diamond branch: `heckeT_p_divN` is by definition the function
`heckeT_p_ut k p hp.pos (⇑f)` bundled as a modular form.

Consumed by `Eigenforms/MainLemma.lean` to instantiate the Miyake 4.6.5
prime-sieve witness
`miyake_4_6_5_prime_sieve_witness_at_pN_one` with the natural choice
`heckeT_p_divN`. -/
theorem qExpansion_one_heckeT_p_divN_coeff
    {M : ℕ} [NeZero M] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpM : ¬ Nat.Coprime p M)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion (1 : ℝ) (heckeT_p_divN k p hp hpM f)).coeff m =
      (qExpansion (1 : ℝ) f).coeff (p * m) := by
  -- `heckeT_p_divN` is the modular-form bundling of the purely upper-triangular
  -- sum `heckeT_p_ut`, so the claim is exactly `hasSum_heckeT_p_ut_period_one`.
  have h1_pos : (0 : ℝ) < 1 := one_pos
  have h1_period : (1 : ℝ) ∈ ((Gamma1 M).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 M).map (mapGL ℝ) = (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  set a := fun n => (qExpansion (1 : ℝ) (⇑f)).coeff n with ha_def
  have hf_hs : ∀ σ : ℍ, HasSum (fun n => a n • (Function.Periodic.qParam (1 : ℝ) ↑σ) ^ n)
      (f σ) := hasSum_qExpansion f h1_pos h1_period
  refine (qExpansion_coeff_unique (c := fun n => a (p * n)) h1_pos h1_period
    (fun τ => ?_) m).symm
  exact hasSum_heckeT_p_ut_period_one k hp (⇑f) a τ hf_hs

end HeckeRing.GL2
