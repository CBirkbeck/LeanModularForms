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
  /- **Proof plan** (using `qExpansion_coeff_unique`):

  Let `a n := (qExpansion N f).coeff n` and define candidate coefficients
  `c m := p^{1-k} · a(pm) + χ(p) · [p|m] · a(m/p)`.

  By `qExpansion_coeff_unique`, it suffices to show:
  `∀ τ : ℍ, HasSum (fun m => c m • 𝕢 N τ ^ m) ((heckeT_p f) τ)`

  This HasSum decomposes via the heckeT_p_fun formula into:

  **Upper-triangular part**: For each `b < p`, `hasSum_qExpansion f` at `(τ+b)/p`
  gives `HasSum (fun n => a n • (𝕢 N ((τ+b)/p))^n) (f((τ+b)/p))`.
  Computing `𝕢 N ((τ+b)/p) = ζ_{pN}^b · w` where `w = 𝕢 (pN) τ`,
  summing over `b` via `HasSum.sum` (finite-infinite exchange),
  and applying `rootOfUnity_sum_eq` to kill non-multiples of `p`:
  `HasSum (fun m => p · a(pm) • q^m) (Σ_b f((τ+b)/p))`, hence after `p^{-k}`:
  `HasSum (fun m => p^{1-k} · a(pm) • q^m) (upper sum)`.

  **Lower/diamond part**: From `hasSum_qExpansion f` at `pτ` using
  `𝕢 N (pτ) = q^p`, and the diamond eigenvalue `⟨p⟩f = χ(p)f`:
  `HasSum (fun m => χ(p) · [p|m] · a(m/p) • q^m) ((⟨p⟩f)(pτ))`.

  Adding the two HasSum's gives the claimed formula. ∎ -/
  -- Prerequisites
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
  have hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    -- The coercion Subgroup SL(2,ℤ) → Subgroup GL(2,ℝ) is map (mapGL ℝ)
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨(N : ℤ), by simp⟩
  -- The proof proceeds by applying qExpansion_coeff_unique: we show the RHS
  -- gives a valid HasSum representation of (T_p f)(τ) for each τ.
  --
  -- Key steps (each uses hasSum_qExpansion + our qParam/orthogonality lemmas):
  -- 1. hasSum_qExpansion f at pτ, with qParam_mul_nat: gives lower/diamond term
  -- 2. hasSum_qExpansion f at (τ+b)/p for each b, with qParam_add: gives shifted sums
  -- 3. hasSum_sum over b = 0,...,p-1: finite-infinite exchange
  -- 4. rootOfUnity_sum_eq: kills non-multiples of p in the sum
  -- 5. HasSum.add: combines upper + lower
  -- 6. qExpansion_coeff_unique: identifies coefficients
  -- Reduce to showing a HasSum representation of (T_p f)(τ)
  suffices key : ∀ τ : ℍ, HasSum
      (fun n : ℕ ↦ ((qExpansion (↑N) (⇑f)).coeff (p * n) +
          (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
            if p ∣ n then (qExpansion (↑N) (⇑f)).coeff (n / p) else 0) •
        Function.Periodic.qParam (↑N) ↑τ ^ n)
      ((heckeT_p k p hp hpN f) τ) by
    exact (qExpansion_coeff_unique hN_pos hN_period key m).symm
  -- The HasSum proof decomposes (T_p f)(τ) into upper + lower terms.
  intro τ
  -- Abbreviate
  set q := Function.Periodic.qParam (↑N) ↑τ with hq_def
  set a := fun n => (qExpansion (↑N) (⇑f)).coeff n with ha_def
  -- Step A: f has a convergent q-expansion at every point in ℍ
  have hf_hs : ∀ σ : ℍ, HasSum (fun n => a n • (Function.Periodic.qParam (↑N) ↑σ) ^ n)
      (f σ) := hasSum_qExpansion f hN_pos hN_period
  -- Step B: HasSum for the lower/diamond term f(pτ)
  -- f(pτ) = Σ a_n (qParam N (pτ))^n = Σ a_n (q^p)^n by qParam_mul_nat
  -- Reindex via n ↦ pn using Function.Injective.hasSum_iff:
  -- HasSum (fun m => [p|m] a_{m/p} • q^m) (f(pτ))
  -- Then scale by χ(p) via HasSum.const_smul
  -- Step C: HasSum for the upper-triangular sum
  -- For each b < p: f((τ+b)/p) = Σ a_n (qParam N ((τ+b)/p))^n
  -- Use qParam_add: qParam N ((τ+b)/p) = qParam N (τ/p) · qParam N (b/p)
  --   where qParam N (b/p) = ζ is a root of unity
  -- Sum over b via hasSum_sum, apply rootOfUnity_sum_eq to Σ_b ζ^{nb}
  -- Surviving terms: p · a_{pm} at index m, after rescaling by p^{-k}
  -- Step B: HasSum for f(pτ)
  have hpτ_im : 0 < ((p : ℂ) * ↑τ).im := by
    simp [Complex.mul_im]; exact mul_pos (Nat.cast_pos.mpr hp.pos) τ.im_pos
  set pτ : ℍ := ⟨(p : ℂ) * ↑τ, hpτ_im⟩
  have h_lower_hs : HasSum (fun n => a n • (q ^ p) ^ n) (f pτ) := by
    have := hf_hs pτ; simp only [pτ] at this; rwa [qParam_mul_nat] at this
  -- Convert (q^p)^n → q^(p*n) for cleaner manipulation
  have h_lower_reindex : HasSum (fun n => a n • q ^ (p * n)) (f pτ) := by
    convert h_lower_hs using 2 with n; rw [← pow_mul]
  -- The remaining steps to close the goal:
  -- 1. Reindex h_lower_reindex via p*n → m using Function.Injective.hasSum_iff
  --    (Nat.mul_left_injective hp.pos), getting HasSum at all m with [p|m] indicator
  -- 2. Scale by χ(p) via HasSum.const_smul (using diamond eigenvalue hf)
  -- 3. Build upper sum: for each b < p, hasSum_qExpansion at (τ+b)/p with
  --    qParam_add to decompose qParam N ((τ+b)/p), then hasSum_sum over b,
  --    then rootOfUnity_sum_eq to collapse the character sum
  -- 4. Scale upper by p^{-k}, reindex via rootOfUnity_sum_eq survivors
  -- 5. HasSum.add upper + lower, matching heckeT_p_fun
  -- Step 3a: Reindex lower term via injection p*· to get [p|m] indicator
  have hinj : Function.Injective (p * · : ℕ → ℕ) := mul_right_injective₀ hp.ne_zero
  have h_lower_ind : HasSum
      (fun m => (if p ∣ m then a (m / p) else 0) • q ^ m) (f pτ) := by
    refine (hinj.hasSum_iff (fun x hx => ?_)).mp ?_
    · simp only [Set.mem_range, not_exists] at hx
      simp [show ¬(p ∣ x) from fun ⟨k, hk⟩ => hx k (by omega)]
    · show HasSum ((fun m => (if p ∣ m then a (m / p) else 0) • q ^ m) ∘ (p * ·)) (f pτ)
      simp only [Function.comp_def, show ∀ n, p ∣ p * n from dvd_mul_right p,
        if_true, Nat.mul_div_cancel_left _ hp.pos]
      convert h_lower_reindex using 2 with n
  -- Step 3b: Scale by χ(p) and connect to diamond term
  set χp := (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) with hχp_def
  set pk := (↑p : ℂ) ^ (k - 1) with hpk_def
  -- Step 2: HasSum for the upper-triangular sum
  -- heckeT_p_ut = Σ_b f ∣[k] T_p_upper b, each slash gives p^{-1} f((τ+b)/p)
  -- (det factor p^{k-1} * denom factor p^{-k} = p^{-1})
  -- After orthogonality over b: coefficient at m is a_{pm}
  have h_upper : HasSum (fun n => a (p * n) • q ^ n)
      (heckeT_p_ut k p hp.pos (⇑f) τ) := by
    -- Decompose: heckeT_p_ut = Σ_b (f ∣[k] T_p_upper b)
    -- Each slash = p⁻¹ * f(σ_b) by slash_T_p_upper_eval
    -- Then: hasSum_sum + qParam decomposition + rootOfUnity_sum_eq + reindex
    -- All ingredients proved above. Assembly requires:
    -- Step 1: heckeT_p_ut(τ) = p⁻¹ * Σ_b f(σ_b) via slash_T_p_upper_eval
    have h_ut_eq : heckeT_p_ut k p hp.pos (⇑f) τ =
        (↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (⟨(↑τ + ↑b) / ↑p, by
          simp; exact div_pos (by linarith [τ.im_pos])
            (Nat.cast_pos.mpr hp.pos)⟩ : ℍ) := by
      simp only [heckeT_p_ut, Finset.sum_apply, Finset.mul_sum]
      congr 1; ext b; exact slash_T_p_upper_eval k p hp b (⇑f) τ
    rw [h_ut_eq]
    -- Remaining: HasSum (fun n => a(pn) • q^n) (p⁻¹ * Σ_b f(σ_b))
    -- Step 2-3: hasSum_sum for finite-infinite exchange
    have h_sum_hs : HasSum
        (fun n => ∑ b ∈ Finset.range p,
          a n • Function.Periodic.qParam (↑N) ↑(glMap (T_p_upper p hp.pos b) • τ) ^ n)
        (∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ)) :=
      hasSum_sum (fun b _ => hf_hs (glMap (T_p_upper p hp.pos b) • τ))
    -- Step 4: Decompose qParam at Möbius action points
    set w := Function.Periodic.qParam (↑N) ((↑τ : ℂ) / ↑p) with hw_def
    set ζ := Function.Periodic.qParam (↑N) (1 / (↑p : ℂ)) with hζ_def
    have h_qparam_decomp : ∀ b ∈ Finset.range p, ∀ n : ℕ,
        Function.Periodic.qParam (↑N) ↑(glMap (T_p_upper p hp.pos b) • τ) ^ n =
        w ^ n * ζ ^ (n * b) := by
      intro b _ n
      have hmob_b : (↑(glMap (T_p_upper p hp.pos b) • τ) : ℂ) = ↑τ / ↑p + ↑b / ↑p := by
        simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom]
        have hdet_pos : 0 < (glMap (T_p_upper p hp.pos b)).det.val := by
          rw [show (glMap (T_p_upper p hp.pos b)).det.val =
            algebraMap ℚ ℝ (T_p_upper p hp.pos b).det.val from
            congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
            GeneralLinearGroup.val_det_apply, T_p_upper_det]; simp; linarith [hp.pos]
        simp only [UpperHalfPlane.σ, hdet_pos, ↓reduceIte, RingHom.id_apply]
        have h00 : (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := by
          simp [glMap, T_p_upper]
        have h01 : (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = b := by
          simp [glMap, T_p_upper]
        have h10 : (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
          simp [glMap, T_p_upper]
        have h11 : (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = p := by
          simp [glMap, T_p_upper, Matrix.cons_val_one]
        simp only [h00, h01, h10, h11]; push_cast; ring
      conv_lhs => rw [show (↑(glMap (T_p_upper p hp.pos b) • τ) : ℂ) = ↑τ / ↑p + ↑b / ↑p
        from hmob_b]
      rw [qParam_add, show (↑b : ℂ) / ↑p = ↑b * (1 / ↑p) from by ring, qParam_mul_nat]
      rw [mul_pow, ← pow_mul, mul_comm b n]
    -- Step 5a: Rewrite h_sum_hs terms using qParam decomposition
    have h_rewritten : HasSum
        (fun n => a n • w ^ n * ∑ b ∈ Finset.range p, ζ ^ (n * b))
        (∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ)) := by
      convert h_sum_hs using 2 with n
      trans (∑ b ∈ Finset.range p, a n * (w ^ n * ζ ^ (n * b)))
      · rw [smul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
      · exact Finset.sum_congr rfl fun b hb => by
          rw [h_qparam_decomp b hb n, smul_eq_mul]
    -- Step 5b: w^p = q, scale by p⁻¹, orthogonality, reindex
    have hp_ne : (↑p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hw_pow_p : w ^ p = q := by
      rw [hw_def, ← qParam_mul_nat]; congr 1; field_simp
    -- Scale h_rewritten by p⁻¹ and match sum values
    have h_scaled := h_rewritten.const_smul (↑p : ℂ)⁻¹
    -- h_scaled has terms p⁻¹ • (a_n • w^n * Σ_b ζ^{nb}) and sum p⁻¹ * Σ_b f(mob_b)
    -- Need to convert to: a(pn) • q^n at the goal's sum value
    -- The term manipulation (orthogonality + reindex + w^{pm}=q^m) and
    -- sum value equality (mob_b τ = ⟨(τ+b)/p, ⋯⟩) close the proof.
    -- Step A: Orthogonality — convert h_scaled terms to indicator form
    have h_ind : HasSum (fun n' => (if p ∣ n' then a n' • w ^ n' else 0))
        ((↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p,
          f (glMap (T_p_upper p hp.pos b) • τ)) := by
      rw [show (↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ) =
          (↑p : ℂ)⁻¹ • ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ) from by
        simp [smul_eq_mul]]
      unfold HasSum at h_scaled ⊢
      refine h_scaled.congr (fun s => ?_)
      congr 1; ext n
      simp only [smul_eq_mul]
      by_cases hn : p ∣ n
      · rw [if_pos hn]
        by_cases ha : a n = 0
        · simp [ha]
        · -- a_n ≠ 0 → N|n (qExpansion periodicity), p|n → pN|n → ζ^n = 1
          have hN_dvd : (N : ℕ) ∣ n := by
            by_contra h_not; exact ha (qExpansion_coeff_eq_zero_of_not_dvd hN_period
              (by rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ))
                from rfl, strictPeriods_Gamma1]; exact ⟨1, by simp⟩) f h_not)
          have hζ_pN : IsPrimitiveRoot ζ (p * N) := by
            rw [hζ_def, Function.Periodic.qParam]
            convert Complex.isPrimitiveRoot_exp (p * N)
              (Nat.mul_ne_zero hp.ne_zero (NeZero.ne N)) using 1
            push_cast; ring
          have hζ_pow : ζ ^ n = 1 := by
            rw [hζ_pN.pow_eq_one_iff_dvd]
            exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hpN hn hN_dvd
          have h_sum_p : ∑ b ∈ Finset.range p, ζ ^ (n * b) = ↑p := by
            simp_rw [pow_mul ζ n, hζ_pow, one_pow, Finset.sum_const, Finset.card_range,
              nsmul_eq_mul, mul_one]
          rw [h_sum_p]; field_simp
      · rw [if_neg hn]
        by_cases ha : a n = 0
        · simp [ha]
        · -- a_n ≠ 0 → N|n, p∤n → ζ^n is nontrivial p-th root → geom sum = 0
          have hζ_pN : IsPrimitiveRoot ζ (p * N) := by
            rw [hζ_def, Function.Periodic.qParam]
            convert Complex.isPrimitiveRoot_exp (p * N)
              (Nat.mul_ne_zero hp.ne_zero (NeZero.ne N)) using 1
            push_cast; ring
          have hN_dvd' : (N : ℕ) ∣ n := by
            by_contra h_not; exact ha (qExpansion_coeff_eq_zero_of_not_dvd hN_period
              (by rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ))
                from rfl, strictPeriods_Gamma1]; exact ⟨1, by simp⟩) f h_not)
          have hζn_ne : ζ ^ n ≠ 1 := by
            intro h_eq
            have := (hζ_pN.pow_eq_one_iff_dvd n).mp h_eq
            -- p * N | n, but p ∤ n — contradiction
            obtain ⟨j, rfl⟩ := hN_dvd'
            have h_p_dvd_j : p ∣ j := by
              rw [show p * N = N * p from by ring] at this
              exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_neZero N) this
            exact hn (h_p_dvd_j.mul_left N)
          have h_sum_zero : ∑ b ∈ Finset.range p, ζ ^ (n * b) = 0 := by
            simp_rw [pow_mul ζ n]
            rw [geom_sum_eq hζn_ne]
            have : (ζ ^ n) ^ p = 1 := by
              -- (ζ^n)^p = ζ^{np}. N|n → exp(2πi·n/N) = exp(2πi·integer) = 1
              have hN_dvd' : (N : ℕ) ∣ n := by
                by_contra h_not; exact ha (qExpansion_coeff_eq_zero_of_not_dvd hN_period
                  (by rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ))
                    from rfl, strictPeriods_Gamma1]; exact ⟨1, by simp⟩) f h_not)
              rw [← pow_mul]
              -- ζ^{np}. ζ is primitive (pN)-th root, need pN | np.
              -- N|n and gcd(p,N)=1 → pN | np (since N|np trivially, p|np trivially)
              have hζ_pN : IsPrimitiveRoot ζ (p * N) := by
                rw [hζ_def, Function.Periodic.qParam]
                convert Complex.isPrimitiveRoot_exp (p * N)
                  (Nat.mul_ne_zero hp.ne_zero (NeZero.ne N)) using 1
                push_cast; ring
              rw [hζ_pN.pow_eq_one_iff_dvd]
              obtain ⟨j, rfl⟩ := hN_dvd'; exact ⟨j, by ring⟩
            simp [this]
          simp [h_sum_zero]
    -- Step B: Reindex via hinj — remove indicator, map n → p*n
    rw [← hinj.hasSum_iff (fun x hx => by
      simp only [Set.mem_range, not_exists] at hx
      simp [show ¬p ∣ x from fun ⟨k, hk⟩ => hx k (by omega)])] at h_ind
    simp only [Function.comp_def, show ∀ m, p ∣ p * m from dvd_mul_right p, if_true] at h_ind
    -- h_ind : HasSum (fun m => a(pm) • w^{pm}) (p⁻¹ * Σ f(mob_b))
    -- Step C: Replace w^{pm} = q^m and match sum values
    convert h_ind using 2 with m'
    · rw [smul_eq_mul, smul_eq_mul, pow_mul, hw_pow_p]
    · symm; exact Finset.sum_congr rfl fun b _ => by
        show f (glMap (T_p_upper p hp.pos b) • τ) = _
        congr 1; ext : 1
        simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom]
        have hdet_pos' : 0 < (glMap (T_p_upper p hp.pos b)).det.val := by
          rw [show (glMap (T_p_upper p hp.pos b)).det.val =
            algebraMap ℚ ℝ (T_p_upper p hp.pos b).det.val from
            congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
            GeneralLinearGroup.val_det_apply, T_p_upper_det]; simp; linarith [hp.pos]
        simp only [UpperHalfPlane.σ, hdet_pos', ↓reduceIte, RingHom.id_apply,
          show (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1
            from by simp [glMap, T_p_upper],
          show (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = b
            from by simp [glMap, T_p_upper],
          show (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0
            from by simp [glMap, T_p_upper],
          show (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = p
            from by simp [glMap, T_p_upper, Matrix.cons_val_one]]
        push_cast; ring
  -- Step 4: The diamond eigenvalue — ⟨p⟩f = χ(p) f for f ∈ M_k(N, χ)
  have h_diamond : ∀ σ : ℍ, (diamondOp k (ZMod.unitOfCoprime p hpN) f) σ = χp • f σ := by
    intro σ
    have hd := (mem_modFormCharSpace_iff k χ f).mp hf (ZMod.unitOfCoprime p hpN)
    change (diamondOpHom k (ZMod.unitOfCoprime p hpN) f) σ = χp • f σ
    rw [hd]; rfl
  -- Step 5: (T_p f)(τ) = upper + slash(lower)
  -- slash(lower) = (⟨p⟩f ∣[k] T_p_lower)(τ) involves det factor p^{k-1} and diamond eigenvalue
  -- Combined: slash(lower) = p^{k-1} * χ(p) * f(pτ)
  have h_slash_lower : (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) τ = pk * χp * f pτ := by
    show ((⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
      glMap (T_p_lower p hp.pos)) τ = pk * χp * f pτ
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
      ext : 1; show (↑(glMap (T_p_lower p hp.pos) • τ) : ℂ) = ↑p * ↑τ
      simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom,
        UpperHalfPlane.σ, hdet_pos, ↓reduceIte, RingHom.id_apply]
      have h00 : (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = p := by
        simp [glMap, T_p_lower]
      have h01 : (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by
        simp [glMap, T_p_lower]
      have h10 : (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
        simp [glMap, T_p_lower]
      have h11 : (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by
        simp [glMap, T_p_lower, Matrix.cons_val_one]
      simp only [h00, h01, h10, h11]; push_cast; ring
    have hdenom : UpperHalfPlane.denom (glMap (T_p_lower p hp.pos)) ↑τ = 1 := by
      simp [UpperHalfPlane.denom, glMap, T_p_lower, Matrix.cons_val_one]
    rw [hσ, RingHom.id_apply, hmob, hdenom, one_zpow, mul_one,
      hdet_val, abs_of_pos (Nat.cast_pos.mpr hp.pos), h_diamond pτ, smul_eq_mul]
    show χp * f pτ * (↑p : ℂ) ^ (k - 1) = pk * χp * f pτ; ring
  -- Scale h_lower_ind by pk * χp
  have h_lower_scaled : HasSum
      (fun m => (pk * χp * if p ∣ m then a (m / p) else 0) • q ^ m)
      (pk * χp * f pτ) := by
    have := h_lower_ind.const_smul (pk * χp)
    simp only [smul_eq_mul] at this ⊢
    convert this using 2 with m; split_ifs <;> ring
  -- Combine upper + lower
  have h_combined := h_upper.add h_lower_scaled
  convert h_combined using 1
  · ext n; simp only [ha_def, smul_eq_mul]; split_ifs <;> ring
  · -- (T_p f)(τ) = heckeT_p_ut(τ) + p^{k-1} χ(p) f(pτ)
    show heckeT_p_fun k p hp hpN f τ = heckeT_p_ut k p hp.pos (⇑f) τ + pk * χp * f pτ
    simp only [heckeT_p_fun, Pi.add_apply, h_slash_lower]

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
  -- Prerequisites (period 1).
  have h1_pos : (0 : ℝ) < 1 := one_pos
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  -- Reduce to showing a HasSum representation of `(T_p f) τ` at period 1.
  suffices key : ∀ τ : ℍ, HasSum
      (fun n : ℕ ↦ ((qExpansion (1 : ℝ) (⇑f)).coeff (p * n) +
          (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
            if p ∣ n then (qExpansion (1 : ℝ) (⇑f)).coeff (n / p) else 0) •
        Function.Periodic.qParam (1 : ℝ) ↑τ ^ n)
      ((heckeT_p k p hp hpN f) τ) by
    exact (qExpansion_coeff_unique h1_pos h1_period key m).symm
  intro τ
  set q := Function.Periodic.qParam (1 : ℝ) ↑τ with hq_def
  set a := fun n => (qExpansion (1 : ℝ) (⇑f)).coeff n with ha_def
  -- Step A: f has a convergent q-expansion at every point in ℍ, period 1.
  have hf_hs : ∀ σ : ℍ, HasSum (fun n => a n • (Function.Periodic.qParam (1 : ℝ) ↑σ) ^ n)
      (f σ) := hasSum_qExpansion f h1_pos h1_period
  -- Step B: HasSum for f(pτ) (lower / diamond term).
  have hpτ_im : 0 < ((p : ℂ) * ↑τ).im := by
    simp [Complex.mul_im]; exact mul_pos (Nat.cast_pos.mpr hp.pos) τ.im_pos
  set pτ : ℍ := ⟨(p : ℂ) * ↑τ, hpτ_im⟩
  have h_lower_hs : HasSum (fun n => a n • (q ^ p) ^ n) (f pτ) := by
    have := hf_hs pτ; simp only [pτ] at this; rwa [qParam_mul_nat] at this
  have h_lower_reindex : HasSum (fun n => a n • q ^ (p * n)) (f pτ) := by
    convert h_lower_hs using 2 with n; rw [← pow_mul]
  have hinj : Function.Injective (p * · : ℕ → ℕ) := mul_right_injective₀ hp.ne_zero
  have h_lower_ind : HasSum
      (fun m => (if p ∣ m then a (m / p) else 0) • q ^ m) (f pτ) := by
    refine (hinj.hasSum_iff (fun x hx => ?_)).mp ?_
    · simp only [Set.mem_range, not_exists] at hx
      simp [show ¬(p ∣ x) from fun ⟨k, hk⟩ => hx k (by omega)]
    · show HasSum ((fun m => (if p ∣ m then a (m / p) else 0) • q ^ m) ∘ (p * ·)) (f pτ)
      simp only [Function.comp_def, show ∀ n, p ∣ p * n from dvd_mul_right p,
        if_true, Nat.mul_div_cancel_left _ hp.pos]
      convert h_lower_reindex using 2 with n
  set χp := (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) with hχp_def
  set pk := (↑p : ℂ) ^ (k - 1) with hpk_def
  -- Step C: HasSum for the upper-triangular sum (with root-of-unity collapse).
  have h_upper : HasSum (fun n => a (p * n) • q ^ n)
      (heckeT_p_ut k p hp.pos (⇑f) τ) := by
    have h_ut_eq : heckeT_p_ut k p hp.pos (⇑f) τ =
        (↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (⟨(↑τ + ↑b) / ↑p, by
          simp; exact div_pos (by linarith [τ.im_pos])
            (Nat.cast_pos.mpr hp.pos)⟩ : ℍ) := by
      simp only [heckeT_p_ut, Finset.sum_apply, Finset.mul_sum]
      congr 1; ext b; exact slash_T_p_upper_eval k p hp b (⇑f) τ
    rw [h_ut_eq]
    have h_sum_hs : HasSum
        (fun n => ∑ b ∈ Finset.range p,
          a n • Function.Periodic.qParam (1 : ℝ) ↑(glMap (T_p_upper p hp.pos b) • τ) ^ n)
        (∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ)) :=
      hasSum_sum (fun b _ => hf_hs (glMap (T_p_upper p hp.pos b) • τ))
    set w := Function.Periodic.qParam (1 : ℝ) ((↑τ : ℂ) / ↑p) with hw_def
    set ζ := Function.Periodic.qParam (1 : ℝ) (1 / (↑p : ℂ)) with hζ_def
    have h_qparam_decomp : ∀ b ∈ Finset.range p, ∀ n : ℕ,
        Function.Periodic.qParam (1 : ℝ) ↑(glMap (T_p_upper p hp.pos b) • τ) ^ n =
        w ^ n * ζ ^ (n * b) := by
      intro b _ n
      have hmob_b : (↑(glMap (T_p_upper p hp.pos b) • τ) : ℂ) = ↑τ / ↑p + ↑b / ↑p := by
        simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom]
        have hdet_pos : 0 < (glMap (T_p_upper p hp.pos b)).det.val := by
          rw [show (glMap (T_p_upper p hp.pos b)).det.val =
            algebraMap ℚ ℝ (T_p_upper p hp.pos b).det.val from
            congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
            GeneralLinearGroup.val_det_apply, T_p_upper_det]; simp; linarith [hp.pos]
        simp only [UpperHalfPlane.σ, hdet_pos, ↓reduceIte, RingHom.id_apply]
        have h00 : (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := by
          simp [glMap, T_p_upper]
        have h01 : (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = b := by
          simp [glMap, T_p_upper]
        have h10 : (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
          simp [glMap, T_p_upper]
        have h11 : (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = p := by
          simp [glMap, T_p_upper, Matrix.cons_val_one]
        simp only [h00, h01, h10, h11]; push_cast; ring
      conv_lhs => rw [show (↑(glMap (T_p_upper p hp.pos b) • τ) : ℂ) = ↑τ / ↑p + ↑b / ↑p
        from hmob_b]
      rw [qParam_add, show (↑b : ℂ) / ↑p = ↑b * (1 / ↑p) from by ring, qParam_mul_nat]
      rw [mul_pow, ← pow_mul, mul_comm b n]
    have h_rewritten : HasSum
        (fun n => a n • w ^ n * ∑ b ∈ Finset.range p, ζ ^ (n * b))
        (∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ)) := by
      convert h_sum_hs using 2 with n
      trans (∑ b ∈ Finset.range p, a n * (w ^ n * ζ ^ (n * b)))
      · rw [smul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
      · exact Finset.sum_congr rfl fun b hb => by
          rw [h_qparam_decomp b hb n, smul_eq_mul]
    have hp_ne : (↑p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hw_pow_p : w ^ p = q := by
      rw [hw_def, ← qParam_mul_nat]; congr 1; field_simp
    have h_scaled := h_rewritten.const_smul (↑p : ℂ)⁻¹
    -- Period-1 simplification: `ζ` is a primitive *p-th* root of unity,
    -- so the orthogonality analysis is direct (no `N | n` case split).
    have hζ_prim : IsPrimitiveRoot ζ p := by
      rw [hζ_def, Function.Periodic.qParam]
      convert Complex.isPrimitiveRoot_exp p hp.ne_zero using 1
      push_cast; ring
    have h_ind : HasSum (fun n' => (if p ∣ n' then a n' • w ^ n' else 0))
        ((↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p,
          f (glMap (T_p_upper p hp.pos b) • τ)) := by
      rw [show (↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ) =
          (↑p : ℂ)⁻¹ • ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ) from by
        simp [smul_eq_mul]]
      unfold HasSum at h_scaled ⊢
      refine h_scaled.congr (fun s => ?_)
      congr 1; ext n
      simp only [smul_eq_mul]
      by_cases hn : p ∣ n
      · rw [if_pos hn]
        -- `p ∣ n` ⟹ `ζ ^ n = 1` directly from primitivity.
        have hζ_pow : ζ ^ n = 1 := by
          rw [hζ_prim.pow_eq_one_iff_dvd]; exact hn
        have h_sum_p : ∑ b ∈ Finset.range p, ζ ^ (n * b) = ↑p := by
          simp_rw [pow_mul ζ n, hζ_pow, one_pow, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, mul_one]
        rw [h_sum_p]; field_simp
      · rw [if_neg hn]
        -- `p ∤ n` ⟹ `ζ ^ n ≠ 1` ⟹ geometric sum collapses.
        have hζn_ne : ζ ^ n ≠ 1 := mt (hζ_prim.pow_eq_one_iff_dvd n).mp hn
        have h_sum_zero : ∑ b ∈ Finset.range p, ζ ^ (n * b) = 0 := by
          simp_rw [pow_mul ζ n]
          rw [geom_sum_eq hζn_ne]
          have hpow : (ζ ^ n) ^ p = 1 := by
            rw [← pow_mul, mul_comm, pow_mul, hζ_prim.pow_eq_one, one_pow]
          simp [hpow]
        simp [h_sum_zero]
    rw [← hinj.hasSum_iff (fun x hx => by
      simp only [Set.mem_range, not_exists] at hx
      simp [show ¬p ∣ x from fun ⟨k, hk⟩ => hx k (by omega)])] at h_ind
    simp only [Function.comp_def, show ∀ m, p ∣ p * m from dvd_mul_right p, if_true] at h_ind
    convert h_ind using 2 with m'
    · rw [smul_eq_mul, smul_eq_mul, pow_mul, hw_pow_p]
    · symm; exact Finset.sum_congr rfl fun b _ => by
        show f (glMap (T_p_upper p hp.pos b) • τ) = _
        congr 1; ext : 1
        simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom]
        have hdet_pos' : 0 < (glMap (T_p_upper p hp.pos b)).det.val := by
          rw [show (glMap (T_p_upper p hp.pos b)).det.val =
            algebraMap ℚ ℝ (T_p_upper p hp.pos b).det.val from
            congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
            GeneralLinearGroup.val_det_apply, T_p_upper_det]; simp; linarith [hp.pos]
        simp only [UpperHalfPlane.σ, hdet_pos', ↓reduceIte, RingHom.id_apply,
          show (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1
            from by simp [glMap, T_p_upper],
          show (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = b
            from by simp [glMap, T_p_upper],
          show (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0
            from by simp [glMap, T_p_upper],
          show (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = p
            from by simp [glMap, T_p_upper, Matrix.cons_val_one]]
        push_cast; ring
  -- Diamond eigenvalue and lower-term slash (identical to period-N version).
  have h_diamond : ∀ σ : ℍ, (diamondOp k (ZMod.unitOfCoprime p hpN) f) σ = χp • f σ := by
    intro σ
    have hd := (mem_modFormCharSpace_iff k χ f).mp hf (ZMod.unitOfCoprime p hpN)
    change (diamondOpHom k (ZMod.unitOfCoprime p hpN) f) σ = χp • f σ
    rw [hd]; rfl
  have h_slash_lower : (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) τ = pk * χp * f pτ := by
    show ((⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
      glMap (T_p_lower p hp.pos)) τ = pk * χp * f pτ
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
      ext : 1; show (↑(glMap (T_p_lower p hp.pos) • τ) : ℂ) = ↑p * ↑τ
      simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom,
        UpperHalfPlane.σ, hdet_pos, ↓reduceIte, RingHom.id_apply]
      have h00 : (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = p := by
        simp [glMap, T_p_lower]
      have h01 : (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by
        simp [glMap, T_p_lower]
      have h10 : (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
        simp [glMap, T_p_lower]
      have h11 : (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by
        simp [glMap, T_p_lower, Matrix.cons_val_one]
      simp only [h00, h01, h10, h11]; push_cast; ring
    have hdenom : UpperHalfPlane.denom (glMap (T_p_lower p hp.pos)) ↑τ = 1 := by
      simp [UpperHalfPlane.denom, glMap, T_p_lower, Matrix.cons_val_one]
    rw [hσ, RingHom.id_apply, hmob, hdenom, one_zpow, mul_one,
      hdet_val, abs_of_pos (Nat.cast_pos.mpr hp.pos), h_diamond pτ, smul_eq_mul]
    show χp * f pτ * (↑p : ℂ) ^ (k - 1) = pk * χp * f pτ; ring
  have h_lower_scaled : HasSum
      (fun m => (pk * χp * if p ∣ m then a (m / p) else 0) • q ^ m)
      (pk * χp * f pτ) := by
    have := h_lower_ind.const_smul (pk * χp)
    simp only [smul_eq_mul] at this ⊢
    convert this using 2 with m; split_ifs <;> ring
  have h_combined := h_upper.add h_lower_scaled
  convert h_combined using 1
  · ext n; simp only [ha_def, smul_eq_mul]; split_ifs <;> ring
  · show heckeT_p_fun k p hp hpN f τ = heckeT_p_ut k p hp.pos (⇑f) τ + pk * χp * f pτ
    simp only [heckeT_p_fun, Pi.add_apply, h_slash_lower]

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
  -- Prerequisites (period 1).
  have h1_pos : (0 : ℝ) < 1 := one_pos
  have h1_period : (1 : ℝ) ∈ ((Gamma1 M).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 M).map (mapGL ℝ) = (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  -- Apply `qExpansion_coeff_unique` at period `1` with the reindexed sequence
  -- `n ↦ (qExpansion 1 f).coeff (p * n)`.
  refine (qExpansion_coeff_unique (c := fun n => (qExpansion (1 : ℝ) f).coeff (p * n))
      h1_pos h1_period (fun τ => ?_) m).symm
  -- `heckeT_p_divN k p hp hpM f` is the modular-form bundling of the
  -- upper-triangular sum `heckeT_p_ut k p hp.pos (⇑f)`.
  change HasSum (fun n => (qExpansion (1 : ℝ) f).coeff (p * n) •
      Function.Periodic.qParam (1 : ℝ) ↑τ ^ n)
    (heckeT_p_ut k p hp.pos (⇑f) τ)
  -- Reuse the period-1 upper-triangular root-of-unity argument from
  -- `fourierCoeff_heckeT_p_period_one`.
  set q := Function.Periodic.qParam (1 : ℝ) ↑τ with hq_def
  set a := fun n => (qExpansion (1 : ℝ) (⇑f)).coeff n with ha_def
  have hf_hs : ∀ σ : ℍ, HasSum (fun n => a n • (Function.Periodic.qParam (1 : ℝ) ↑σ) ^ n)
      (f σ) := hasSum_qExpansion f h1_pos h1_period
  have hinj : Function.Injective (p * · : ℕ → ℕ) := mul_right_injective₀ hp.ne_zero
  -- Step 1: Rewrite `heckeT_p_ut` as `p⁻¹ * Σ_b f(σ_b)` via `slash_T_p_upper_eval`.
  have h_ut_eq : heckeT_p_ut k p hp.pos (⇑f) τ =
      (↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (⟨(↑τ + ↑b) / ↑p, by
        simp; exact div_pos (by linarith [τ.im_pos])
          (Nat.cast_pos.mpr hp.pos)⟩ : ℍ) := by
    simp only [heckeT_p_ut, Finset.sum_apply, Finset.mul_sum]
    congr 1; ext b; exact slash_T_p_upper_eval k p hp b (⇑f) τ
  rw [h_ut_eq]
  -- Step 2: Assemble the HasSum of the sum over `b` via finite-infinite exchange.
  have h_sum_hs : HasSum
      (fun n => ∑ b ∈ Finset.range p,
        a n • Function.Periodic.qParam (1 : ℝ) ↑(glMap (T_p_upper p hp.pos b) • τ) ^ n)
      (∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ)) :=
    hasSum_sum (fun b _ => hf_hs (glMap (T_p_upper p hp.pos b) • τ))
  -- Step 3: Decompose `qParam 1 (σ_b τ) = w · ζ^b` where `w = qParam 1 (τ/p)`
  -- and `ζ = qParam 1 (1/p)` is a primitive `p`-th root of unity.
  set w := Function.Periodic.qParam (1 : ℝ) ((↑τ : ℂ) / ↑p) with hw_def
  set ζ := Function.Periodic.qParam (1 : ℝ) (1 / (↑p : ℂ)) with hζ_def
  have h_qparam_decomp : ∀ b ∈ Finset.range p, ∀ n : ℕ,
      Function.Periodic.qParam (1 : ℝ) ↑(glMap (T_p_upper p hp.pos b) • τ) ^ n =
      w ^ n * ζ ^ (n * b) := by
    intro b _ n
    have hmob_b : (↑(glMap (T_p_upper p hp.pos b) • τ) : ℂ) = ↑τ / ↑p + ↑b / ↑p := by
      simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom]
      have hdet_pos : 0 < (glMap (T_p_upper p hp.pos b)).det.val := by
        rw [show (glMap (T_p_upper p hp.pos b)).det.val =
          algebraMap ℚ ℝ (T_p_upper p hp.pos b).det.val from
          congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
          GeneralLinearGroup.val_det_apply, T_p_upper_det]; simp; linarith [hp.pos]
      simp only [UpperHalfPlane.σ, hdet_pos, ↓reduceIte, RingHom.id_apply]
      have h00 : (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := by
        simp [glMap, T_p_upper]
      have h01 : (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = b := by
        simp [glMap, T_p_upper]
      have h10 : (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
        simp [glMap, T_p_upper]
      have h11 : (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = p := by
        simp [glMap, T_p_upper, Matrix.cons_val_one]
      simp only [h00, h01, h10, h11]; push_cast; ring
    conv_lhs => rw [show (↑(glMap (T_p_upper p hp.pos b) • τ) : ℂ) = ↑τ / ↑p + ↑b / ↑p
      from hmob_b]
    rw [qParam_add, show (↑b : ℂ) / ↑p = ↑b * (1 / ↑p) from by ring, qParam_mul_nat]
    rw [mul_pow, ← pow_mul, mul_comm b n]
  have h_rewritten : HasSum
      (fun n => a n • w ^ n * ∑ b ∈ Finset.range p, ζ ^ (n * b))
      (∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ)) := by
    convert h_sum_hs using 2 with n
    trans (∑ b ∈ Finset.range p, a n * (w ^ n * ζ ^ (n * b)))
    · rw [smul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
    · exact Finset.sum_congr rfl fun b hb => by
        rw [h_qparam_decomp b hb n, smul_eq_mul]
  -- Step 4: `w^p = q` and primitive-root orthogonality collapse the `b`-sum.
  have hp_ne : (↑p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hw_pow_p : w ^ p = q := by
    rw [hw_def, ← qParam_mul_nat]; congr 1; field_simp
  have h_scaled := h_rewritten.const_smul (↑p : ℂ)⁻¹
  have hζ_prim : IsPrimitiveRoot ζ p := by
    rw [hζ_def, Function.Periodic.qParam]
    convert Complex.isPrimitiveRoot_exp p hp.ne_zero using 1
    push_cast; ring
  -- Step 5: Orthogonality collapses the summand to the `p ∣ n` indicator form.
  have h_ind : HasSum (fun n' => (if p ∣ n' then a n' • w ^ n' else 0))
      ((↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p,
        f (glMap (T_p_upper p hp.pos b) • τ)) := by
    rw [show (↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ) =
        (↑p : ℂ)⁻¹ • ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ) from by
      simp [smul_eq_mul]]
    unfold HasSum at h_scaled ⊢
    refine h_scaled.congr (fun s => ?_)
    congr 1; ext n
    simp only [smul_eq_mul]
    by_cases hn : p ∣ n
    · rw [if_pos hn]
      have hζ_pow : ζ ^ n = 1 := by
        rw [hζ_prim.pow_eq_one_iff_dvd]; exact hn
      have h_sum_p : ∑ b ∈ Finset.range p, ζ ^ (n * b) = ↑p := by
        simp_rw [pow_mul ζ n, hζ_pow, one_pow, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
      rw [h_sum_p]; field_simp
    · rw [if_neg hn]
      have hζn_ne : ζ ^ n ≠ 1 := mt (hζ_prim.pow_eq_one_iff_dvd n).mp hn
      have h_sum_zero : ∑ b ∈ Finset.range p, ζ ^ (n * b) = 0 := by
        simp_rw [pow_mul ζ n]
        rw [geom_sum_eq hζn_ne]
        have hpow : (ζ ^ n) ^ p = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hζ_prim.pow_eq_one, one_pow]
        simp [hpow]
      simp [h_sum_zero]
  -- Step 6: Reindex the indicator sum via `m ↦ p*m` and equate with the goal.
  rw [← hinj.hasSum_iff (fun x hx => by
    simp only [Set.mem_range, not_exists] at hx
    simp [show ¬p ∣ x from fun ⟨k, hk⟩ => hx k (by omega)])] at h_ind
  simp only [Function.comp_def, show ∀ m, p ∣ p * m from dvd_mul_right p, if_true] at h_ind
  convert h_ind using 2 with m'
  · rw [smul_eq_mul, smul_eq_mul, pow_mul, hw_pow_p]
  · symm; exact Finset.sum_congr rfl fun b _ => by
      show f (glMap (T_p_upper p hp.pos b) • τ) = _
      congr 1; ext : 1
      simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom]
      have hdet_pos' : 0 < (glMap (T_p_upper p hp.pos b)).det.val := by
        rw [show (glMap (T_p_upper p hp.pos b)).det.val =
          algebraMap ℚ ℝ (T_p_upper p hp.pos b).det.val from
          congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
          GeneralLinearGroup.val_det_apply, T_p_upper_det]; simp; linarith [hp.pos]
      simp only [UpperHalfPlane.σ, hdet_pos', ↓reduceIte, RingHom.id_apply,
        show (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1
          from by simp [glMap, T_p_upper],
        show (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = b
          from by simp [glMap, T_p_upper],
        show (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0
          from by simp [glMap, T_p_upper],
        show (↑(glMap (T_p_upper p hp.pos b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = p
          from by simp [glMap, T_p_upper, Matrix.cons_val_one]]
      push_cast; ring

end HeckeRing.GL2
