/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.SlashActionAuxil
import LeanModularForms.Eigenforms.ConductorTheorem
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import LeanModularForms.HeckeRIngs.GL2.Newforms.BadPrimeReduction

/-!
# Newforms, eigenforms, and oldforms (Phase 6)

This file develops the theory of newforms following Diamond–Shurman §5.6–5.8
and Atkin–Lehner [AL70].

## Design

Following the Mathlib convention where `CuspForm` extends `SlashInvariantForm`,
we define `Eigenform`, `Newform`, and `Oldform` as structures **extending**
`CuspForm`, plus supporting predicates `IsEigenform`, `IsNewform`, `IsOldform`.

The structure-based approach makes it easy to:
- Pass an eigenform as a cusp form (via the auto-generated `toCuspForm` projection)
- Speak of "the eigenvalues of f" as field access
- Define submodules `cuspFormsOld` and `cuspFormsNew` as the carrier sets

## Main definitions

### Structures extending CuspForm
* `Eigenform N k` — a cusp form together with eigenvalue data for all T_n with (n,N)=1
* `Newform N k` — an eigenform that is in the new subspace and is normalised (a_1 = 1)

### Predicates
* `IsEigenform f` — f is a common Hecke eigenform
* `IsOldform f` — f is in the span of level-raised forms from proper divisors
* `IsNewform f` — f is a newform (eigen + new + normalised)

### Submodules
* `cuspFormsOld` — submodule of oldforms
* `cuspFormsNew` — submodule of newforms (orthogonal complement)

## Main results

* `cuspFormsOld_isCompl_cuspFormsNew` — DS (5.20): direct sum decomposition
* `heckeT_n_preserves_cuspFormsOld/New` — DS Prop 5.6.2
* `newform_unique` — DS Thm 5.8.2 (Atkin-Lehner uniqueness)
* `mainLemma` — DS Thm 5.7.1 (Atkin-Lehner main lemma)
* `strongMultiplicityOne` — the goal of the project

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §§5.6–5.8
* [AL70] Atkin–Lehner, "Hecke operators on Γ₀(m)", Math. Ann. 185 (1970)
* [Miy] Miyake, *Modular Forms*, §4.6
-/


/-!
## Module organisation

This file was split into focused submodules under `Newforms/`; it now re-exports
the whole chain (via `Newforms.BadPrimeReduction`) and hosts the final SMO
consumers.  The submodules, in import order, are:
`Newforms.Basic`, `Newforms.LevelRaiseComm`, `Newforms.MainLemma`,
`Newforms.CoeffSeq`, `Newforms.Fricke`, `Newforms.FrickeTwist`,
`Newforms.MellinBridges`, `Newforms.BadPrimeAdjoint`, `Newforms.BadPrimeCosets`,
`Newforms.BadPrimeReduction`.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}
/-! ### T181: strictly-lower bridges from the (q, b) aggregate bijection residual

After T177/T178/T179/T180, the only blocker for unconditional bad-prime
Hecke-Petersson adjoint identity is the substantive `(q, b)`-aggregate
Atkin-Lehner reindex. T165 already gave a clean Lean signature
`Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBBijection` for this
content (an explicit `Equiv` on `(SL(2, ℤ) ⧸ Γ₁(N)) × Fin p` plus per-`(q, b)`
summand equality), and bridges
* `qBBijection ⟹ qBDomainSwap` (T165 forward),
* `qBDomainSwap ⟹ qBSimplified` (T164 forward),
* `qBSimplified ⟹ qBExpanded` (T163 forward),
* `qBExpanded ⟹ DoubleCosetTileBridge` (T162 forward),
* `DoubleCosetTileBridge ⟹ Intertwine` (T161 forward),
* `Intertwine ⟹ BSum` (T160 chain forward).

T181 composes these into a single named bridge `qBBijection ⟹ BSum`, and
chains with the T159 forward bridge `BSum ⟹ HasBadPrimeFrickePetNAdjoint`
(`hasBadPrimeFrickePetNAdjoint_of_qBDoubleSumIdentity`) to expose
`qBBijection ⟹ HasBadPrimeFrickePetNAdjoint`.

The remaining substantive math is the construction of the `Equiv` on
`(SL(2, ℤ) ⧸ Γ₁(N)) × Fin p` from the matrix relation `M_b · W_N = W_N · β_b`
(`Newform.frickeMatrix_mul_glMap_T_p_upper_eq_lower_offset_mul_frickeMatrix`).
This is the classical Atkin-Lehner / Γ₁(N) double-coset content, mirroring
Diamond-Shurman §5.5 and Miyake §4.6.5. -/

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **T181 strictly-lower bridge: `qBBijection ⟹ BSum` via the existing
T160-T165 chain.**

The premise `Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBBijection`
is the substantive `(q, b)`-aggregate Atkin-Lehner reindex content; once it
holds, this bridge gives the BSum residual mechanically through the existing
T160-T165 chain compositions.

Importantly, this theorem does **not assume** the forbidden residuals
`HasBadPrimeFrickePetNAdjoint`, `HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBSimplified`,
or `HasBadPrimePetN_T_p_FrickeAdjoint_BSum`; the chain composes them as
intermediates derived from `qBBijection`.

The remaining theorem to make this fully unconditional is the construction of
`Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBBijection N k p hp hpN`
itself: an explicit `Equiv σ : (SL(2, ℤ) ⧸ Γ₁(N)) × Fin p ≃
(SL(2, ℤ) ⧸ Γ₁(N)) × Fin p` together with the per-`(q, b)` summand identity
witnessed by the matrix relation `M_b · W_N = W_N · β_b`. -/
theorem Newform.hasBadPrimePetN_T_p_FrickeAdjoint_BSum_of_qBBijection
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h_bij :
      Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBBijection N k p hp hpN) :
    Newform.HasBadPrimePetN_T_p_FrickeAdjoint_BSum N k p hp hpN :=
  Newform.hasBadPrimePetN_T_p_FrickeAdjoint_BSum_of_intertwine hp hpN
    (Newform.hasBadPrimePetN_T_p_FrickeAdjoint_Intertwine_of_doubleCosetTileBridge hp hpN
      (Newform.hasBadPrimeAtkinLehnerDoubleCosetTileBridge_of_qBExpanded hp hpN
        (Newform.hasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBExpanded_of_qBSimplified hp hpN
          (Newform.hasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBSimplified_of_qBDomainSwap hp hpN
            (Newform.hasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBDomainSwap_of_qBBijection hp hpN
              h_bij)))))

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **T181: `qBBijection ⟹ HasBadPrimeFrickePetNAdjoint`.**

Composes the T181 strictly-lower bridge `BSum_of_qBBijection` with the T159
forward bridge `hasBadPrimeFrickePetNAdjoint_of_qBDoubleSumIdentity`. -/
theorem Newform.hasBadPrimeFrickePetNAdjoint_of_qBBijection
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h_bij :
      Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBBijection N k p hp hpN) :
    Newform.HasBadPrimeFrickePetNAdjoint N k p :=
  Newform.hasBadPrimeFrickePetNAdjoint_of_qBDoubleSumIdentity hp hpN
    (Newform.hasBadPrimePetN_T_p_FrickeAdjoint_BSum_of_qBBijection hp hpN h_bij)

/-- **Full Newform Euler product on `Re s > k/2 + 1` from full coprime
multiplicativity (T138 helper).**

Generic `EulerProduct.eulerProduct_hasProd` instantiation for the Newform
Fourier coefficient sequence `f.lCoeff` under the strengthened
multiplicativity hypothesis: full coprime multiplicativity (no
level-coprime restriction).  Mirrors `Newform.lSeries_stripped_hasProd`
but applied to the **un-stripped** sequence. -/
theorem Newform.lSeries_full_hasProd_of_full_coprime_mul
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (h_full_mul : ∀ {m n : ℕ}, Nat.Coprime m n →
      f.lCoeff (m * n) = f.lCoeff m * f.lCoeff n)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasProd
      (fun p : Nat.Primes => ∑' e : ℕ, LSeries.term f.lCoeff s ((p : ℕ) ^ e))
      (LSeries f.lCoeff s) := by
  set g : ℕ → ℂ := LSeries.term f.lCoeff s with hg_def
  have h_g_zero : g 0 = 0 := by
    show LSeries.term f.lCoeff s 0 = 0; rfl
  have h_g_one : g 1 = 1 := by
    show LSeries.term f.lCoeff s 1 = 1
    rw [LSeries.term_def, if_neg one_ne_zero, f.lCoeff_one,
      Nat.cast_one, Complex.one_cpow, div_one]
  have h_g_mul : ∀ {m n : ℕ}, m.Coprime n → g (m * n) = g m * g n := by
    intro m n hmn
    show LSeries.term f.lCoeff s (m * n) =
      LSeries.term f.lCoeff s m * LSeries.term f.lCoeff s n
    rw [LSeries.term_def₀ f.lCoeff_zero, LSeries.term_def₀ f.lCoeff_zero,
      LSeries.term_def₀ f.lCoeff_zero, h_full_mul hmn]
    push_cast
    rw [Complex.natCast_mul_natCast_cpow]; ring
  have h_g_summ : Summable fun n => ‖g n‖ := (f.lSeriesSummable hs).norm
  exact EulerProduct.eulerProduct_hasProd h_g_one h_g_mul h_g_summ h_g_zero

/-- **Per-term identity at a prime under the bad-prime closed form (T138
helper).** -/
private lemma Newform.term_lCoeff_pow_of_bad_prime_pow
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    {p : ℕ} (hp : p.Prime)
    (h_bad_pow : ∀ r : ℕ, f.lCoeff (p ^ r) = f.lCoeff p ^ r)
    (s : ℂ) (e : ℕ) :
    LSeries.term f.lCoeff s (p ^ e) =
      (f.lCoeff p * (p : ℂ) ^ (-s)) ^ e := by
  rw [LSeries.term_def₀ f.lCoeff_zero, h_bad_pow e]
  -- `p ≥ 2`, hence `(p : ℂ) ≠ 0`.
  have hp_ne : ((p : ℕ) : ℂ) ≠ 0 := by
    have h_nat : (p : ℕ) ≠ 0 := hp.pos.ne'
    exact_mod_cast h_nat
  -- `((p : ℂ) ^ e) ^ s = (p : ℂ) ^ (e * s)` for natural `e`.
  -- Then `((p : ℂ) ^ s) ^ e = (p : ℂ) ^ (e * s)` similarly,
  -- so we use the swap `((p : ℂ) ^ e) ^ (-s) = ((p : ℂ) ^ (-s)) ^ e`.
  have h_swap : ((p : ℂ) ^ e) ^ (-s) = ((p : ℂ) ^ (-s)) ^ e := by
    rw [← Complex.natCast_cpow_natCast_mul (p : ℕ) e (-s),
      show ((e : ℂ) * (-s)) = (-s) * (e : ℂ) from by ring,
      Complex.cpow_mul_nat]
  push_cast
  rw [mul_pow, h_swap]

/-- **Bad-prime geometric sum from cusp summability + closed form (T138
helper).** -/
private lemma Newform.tsum_term_lCoeff_pow_at_bad_prime_eq_geom
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    {p : ℕ} (hp : p.Prime)
    (h_bad_pow : ∀ r : ℕ, f.lCoeff (p ^ r) = f.lCoeff p ^ r)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    ‖f.lCoeff p * (p : ℂ) ^ (-s)‖ < 1 ∧
    ∑' e : ℕ, LSeries.term f.lCoeff s ((p : ℕ) ^ e) =
      (1 - f.lCoeff p * (p : ℂ) ^ (-s))⁻¹ := by
  have h_term : ∀ e : ℕ, LSeries.term f.lCoeff s ((p : ℕ) ^ e) =
      (f.lCoeff p * ((p : ℕ) : ℂ) ^ (-s)) ^ e :=
    fun e => f.term_lCoeff_pow_of_bad_prime_pow hp h_bad_pow s e
  -- Pull subset summability from full cusp summability via `Summable.comp_injective`
  -- with the injection `e ↦ p ^ e` (injective since `p ≥ 2`).
  have h_p_pow_inj : Function.Injective fun e : ℕ => (p : ℕ) ^ e := by
    intro a b hab
    exact Nat.pow_right_injective hp.two_le hab
  have h_sum_full : Summable fun n : ℕ => ‖LSeries.term f.lCoeff s n‖ :=
    (f.lSeriesSummable hs).norm
  have h_sum_pow : Summable fun e : ℕ =>
      ‖LSeries.term f.lCoeff s ((p : ℕ) ^ e)‖ :=
    h_sum_full.comp_injective h_p_pow_inj
  -- Substitute the per-term identity and conclude `‖r‖ < 1` from geometric
  -- summability.
  have h_sum_geom : Summable fun e : ℕ =>
      ‖(f.lCoeff p * ((p : ℕ) : ℂ) ^ (-s)) ^ e‖ := by
    refine h_sum_pow.congr (fun e => ?_)
    rw [h_term e]
  have h_sum_pow_geom : Summable fun e : ℕ =>
      (f.lCoeff p * ((p : ℕ) : ℂ) ^ (-s)) ^ e :=
    Summable.of_norm h_sum_geom
  have h_norm_lt : ‖f.lCoeff p * ((p : ℕ) : ℂ) ^ (-s)‖ < 1 :=
    summable_geometric_iff_norm_lt_one.mp h_sum_pow_geom
  refine ⟨h_norm_lt, ?_⟩
  -- Use tsum_geometric_of_norm_lt_one.
  rw [tsum_congr h_term, tsum_geometric_of_norm_lt_one h_norm_lt]

/-- **Constructor for `Newform.EulerStrippingArithmeticInput` from the bundled
Hecke multiplicative structure (T138 strict reduction).**

Builds an instance of `Newform.EulerStrippingArithmeticInput f χ` from the
single named arithmetic input `Newform.HasHeckeMultiplicativeStructure f χ`.

**Construction.**
* `S` — the bad-prime Finset `{p : Nat.Primes | (p : ℕ) ∣ N}`, lifted from
  `Nat.primeFactors N` via `Finset.attach.image`.
* `hf_full_euler` — `Newform.lSeries_full_hasProd_of_full_coprime_mul`
  applied to `h.full_coprime_mul`.
* `h_bad_local_inv` — `Newform.tsum_term_lCoeff_pow_at_bad_prime_eq_geom`
  applied to `h.bad_prime_pow` at each `p ∈ S`.
* `h_bad_local_ne_zero` — same helper plus `‖r‖ < 1 → 1 - r ≠ 0`.

**T138 status: complete.**  This theorem closes the strict reduction from
T137: chaining
`Newform.eulerStrippingArithmeticInput_of_heckeStruct` →
`Newform.hasEulerStrippingMultiplier_of_arithmeticInput` produces
`Newform.HasEulerStrippingMultiplier f` from any
`Newform.HasHeckeMultiplicativeStructure f χ` instance.

**Remaining classical input.**  An instance of
`Newform.HasHeckeMultiplicativeStructure f χ` for every newform / character
pair is the **last classical arithmetic input** for H1b.  The two fields
correspond to two named classical theorems (Diamond–Shurman §5.8
Prop 5.8.5 / Miyake §4.5.16):

1. Full coprime multiplicativity of normalised Hecke eigenform Fourier
   coefficients (extending `Newform.lCoeff_mul_of_coprime` past
   both-coprime-to-`N`).
2. Bad-prime Hecke recurrence `f(p^{r+1}) = a_p · f(p^r)` at `p ∣ N`,
   yielding the closed form `f(p^r) = a_p^r`. -/
noncomputable def Newform.eulerStrippingArithmeticInput_of_heckeStruct
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (h : Newform.HasHeckeMultiplicativeStructure f χ) :
    Newform.EulerStrippingArithmeticInput f χ where
  hfχ := h.hfχ
  S := (Nat.primeFactors N).attach.image
    (fun ⟨p, hp⟩ => ⟨p, (Nat.mem_primeFactors.mp hp).1⟩)
  hS := by
    intro p
    constructor
    · intro hp_S
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
        Nat.mem_primeFactors] at hp_S
      obtain ⟨q, ⟨hq_prime, hq_N, _hN_ne⟩, hq_eq⟩ := hp_S
      have h_eq : (p : ℕ) = q := by
        have := congr_arg (fun (x : Nat.Primes) => (x : ℕ)) hq_eq.symm
        simpa using this
      rw [h_eq]; exact hq_N
    · intro hp_dvd
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
        Nat.mem_primeFactors]
      exact ⟨(p : ℕ), ⟨p.prop, hp_dvd, NeZero.ne N⟩, rfl⟩
  hf_full_euler := fun {s} hs =>
    f.lSeries_full_hasProd_of_full_coprime_mul h.full_coprime_mul hs
  h_bad_local_inv := by
    intro s hs p hp_S
    have hp_dvd : (p : ℕ) ∣ N := by
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
        Nat.mem_primeFactors] at hp_S
      obtain ⟨q, ⟨_, hq_N, _⟩, hq_eq⟩ := hp_S
      have h_eq : (p : ℕ) = q := by
        have := congr_arg (fun (x : Nat.Primes) => (x : ℕ)) hq_eq.symm
        simpa using this
      rw [h_eq]; exact hq_N
    exact (f.tsum_term_lCoeff_pow_at_bad_prime_eq_geom p.prop
      (h.bad_prime_pow p.prop hp_dvd) hs).2
  h_bad_local_ne_zero := by
    intro s hs p hp_S
    have hp_dvd : (p : ℕ) ∣ N := by
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
        Nat.mem_primeFactors] at hp_S
      obtain ⟨q, ⟨_, hq_N, _⟩, hq_eq⟩ := hp_S
      have h_eq : (p : ℕ) = q := by
        have := congr_arg (fun (x : Nat.Primes) => (x : ℕ)) hq_eq.symm
        simpa using this
      rw [h_eq]; exact hq_N
    have h_norm := (f.tsum_term_lCoeff_pow_at_bad_prime_eq_geom p.prop
      (h.bad_prime_pow p.prop hp_dvd) hs).1
    -- `‖r‖ < 1 ⟹ 1 - r ≠ 0`.
    intro h_eq_zero
    have h_eq_one : f.lCoeff (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s) = 1 :=
      (sub_eq_zero.mp h_eq_zero).symm
    rw [h_eq_one, norm_one] at h_norm
    exact lt_irrefl 1 h_norm

/-- **`Newform.HasEulerStrippingMultiplier` from the bundled Hecke
multiplicative structure (T138 final assembly).**

Chains `Newform.eulerStrippingArithmeticInput_of_heckeStruct` (T138) with
`Newform.hasEulerStrippingMultiplier_of_arithmeticInput` (T137) to produce
H1b directly from the **single named arithmetic input**
`Newform.HasHeckeMultiplicativeStructure f χ`.

This is the **shortest H1b consumer**: callers supply one bundled hypothesis,
and the entire H1b predicate `Newform.HasEulerStrippingMultiplier f` is
delivered. -/
theorem Newform.hasEulerStrippingMultiplier_of_heckeStruct
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (h : Newform.HasHeckeMultiplicativeStructure f χ) :
    Newform.HasEulerStrippingMultiplier f :=
  f.hasEulerStrippingMultiplier_of_arithmeticInput χ
    (f.eulerStrippingArithmeticInput_of_heckeStruct χ h)

/-- **`Newform.CompletedFrickeData` from the two named classical inputs (T136
strict reduction).**

Strict reduction theorem: a `Newform.CompletedFrickeData f` exists for
any newform `f : Newform N k` (with `0 < (k : ℝ)`) given the two named
residual classical inputs:

1. `Newform.HasFrickeTwistAsCuspForm f` — Atkin-Lehner Fricke twist as a
   CuspForm-valued object plus slash equality (named H1a).
2. `Newform.HasEulerStrippingMultiplier f` — Euler-stripping multiplier
   plus entire and bridge equation (named H1b).

This is the deepest Mellin/Fricke-side reduction on the corrected
(post-T133/T134/T135) analytic chain: the H1 side of
`Newform.HeckeEntireExtension` factors through `CompletedFrickeData`,
which itself factors through these two named classical predicates via
`Newform.CompletedFrickeData.ofSlashEqWithStripping`.  All other H1
fields (`pair : StrongFEPair ℂ`, `completed_bridge`, decay/integrability)
are mechanically discharged by existing infrastructure
(`Newform.imAxis_feq_of_slashEq`, `Newform.imAxis_rapidDecay`,
`Newform.locallyIntegrableOn_imAxis`, `Newform.hasCompletedMellinIdentity`). -/
theorem Newform.completedFrickeData_of_classicalInputs
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (h_fricke : Newform.HasFrickeTwistAsCuspForm f)
    (hk_pos : 0 < (k : ℝ))
    (h_stripping : Newform.HasEulerStrippingMultiplier f) :
    Nonempty (Newform.CompletedFrickeData f) := by
  obtain ⟨twist, slash_eq⟩ := h_fricke
  obtain ⟨stripping, stripping_diff, stripping_bridge⟩ := h_stripping
  exact ⟨Newform.CompletedFrickeData.ofSlashEqWithStripping f twist slash_eq hk_pos
    stripping stripping_diff stripping_bridge⟩

/-- **Build `Newform.CompletedMellinData` from `CompletedFrickeData` (T134).**

Projection constructor: discards the slash-side data (`twist`, `slash_eq`)
and exposes only the analytic-content fields needed by
`Newform.HeckeEntireExtension_of_CompletedMellinData`. -/
noncomputable def Newform.CompletedMellinData.ofCompletedFrickeData
    {N : ℕ} [NeZero N] {k : ℤ} {f : Newform N k}
    (data : Newform.CompletedFrickeData f) : Newform.CompletedMellinData f where
  pair := data.pair
  hk_pos := data.hk_pos
  completed_bridge := data.completed_bridge
  stripping := data.stripping
  stripping_diff := data.stripping_diff
  stripping_bridge := data.stripping_bridge

/-- **Global `Newform.HeckeEntireExtension` from per-newform
`Newform.CompletedFrickeData` (T134, honest analytic input).**

Chains through `Newform.HeckeEntireExtension_of_CompletedMellinData` (T133)
via the projection `CompletedMellinData.ofCompletedFrickeData`.  Replaces
`Newform.HeckeEntireExtension_of_FrickeSlashData` (T132) which routed
through the mathematically false raw bridge. -/
theorem Newform.HeckeEntireExtension_of_CompletedFrickeData
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.CompletedFrickeData f) :
    Newform.HeckeEntireExtension :=
  Newform.HeckeEntireExtension_of_CompletedMellinData
    (fun _N _ _k f => Newform.CompletedMellinData.ofCompletedFrickeData (h f))

/-- **Global `Newform.HeckeEntireExtension` from the two named classical
inputs (T136).**

Top-level chain: combining the per-newform classical inputs (via
`Newform.completedFrickeData_of_classicalInputs`) with the existing
`Newform.HeckeEntireExtension_of_CompletedFrickeData` (T134) yields the
global `Newform.HeckeEntireExtension` predicate.  This is the **complete
Mellin/Fricke-side reduction** of `Newform.HeckeEntireExtension` to the
two named classical analytic inputs `HasFrickeTwistAsCuspForm` and
`HasEulerStrippingMultiplier`. -/
theorem Newform.HeckeEntireExtension_of_classicalInputs
    (h_fricke : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.HasFrickeTwistAsCuspForm f)
    (h_pos : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (_f : Newform N k), 0 < (k : ℝ))
    (h_stripping : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.HasEulerStrippingMultiplier f) :
    Newform.HeckeEntireExtension :=
  Newform.HeckeEntireExtension_of_CompletedFrickeData
    (fun _N _ _k f =>
      (Newform.completedFrickeData_of_classicalInputs f
        (h_fricke f) (h_pos f) (h_stripping f)).some)

/-- **`Newform.AnalyticContradiction` from per-newform
`Newform.CompletedFrickeData` + `PerNewformFullDirichletData` (T134 H1+H2
consumer, honest analytic input).**

Replaces `Newform.analyticContradiction_of_FrickeSlashData_of_PerNewformFullDirichletData`
(which used the false raw bridge) with the honest analytic input. -/
theorem Newform.analyticContradiction_of_CompletedFrickeData_of_PerNewformFullDirichletData
    (h_fricke : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.CompletedFrickeData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S) :
    Newform.AnalyticContradiction := by
  have h_no_ext : Newform.NoEntireExtensionUnderBadPrime :=
    Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate
      (fun N _ k f χ hfχ S h_bad =>
        Newform.full_pole_witness_data_of_PerNewformFullDirichletData f χ S
          (h_data f χ hfχ S h_bad))
  exact Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
    (Newform.HeckeEntireExtension_of_CompletedFrickeData h_fricke) h_no_ext

/-- **Existence of nonzero prime-eigenvalue from per-newform
`CompletedFrickeData` + `PerNewformFullDirichletData` (T134 H1+H2 consumer,
honest analytic input). -/
theorem Newform.exists_nonzero_prime_eigenvalue_of_CompletedFrickeData_of_PerNewformFullDirichletData
    (h_fricke : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.CompletedFrickeData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S)
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, Nat.Coprime q N ∧ q ∉ S ∧
      f.eigenvalue ⟨q, hq.pos⟩ ≠ 0 :=
  Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction
    (Newform.analyticContradiction_of_CompletedFrickeData_of_PerNewformFullDirichletData
      h_fricke h_data) f χ hfχ S

/-- **SMO endpoint: per-newform `CompletedFrickeData` +
`PerNewformFullDirichletData` + `newform_unique` (T134 H1+H2 endpoint, honest
analytic input).**

Top-level SMO endpoint, replacing
`strongMultiplicityOne_of_FrickeSlashData_of_PerNewformFullDirichletData_of_newformUnique`
(T132) with the honest classical Hecke 1936 Mellin–Dirichlet identity (Gamma
factor + full `lCoeff`) plus the finite Euler-stripping bridge. -/
theorem strongMultiplicityOne_of_CompletedFrickeData_of_PerNewformFullDirichletData_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_fricke : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.CompletedFrickeData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  have h_ana : Newform.AnalyticContradiction :=
    Newform.analyticContradiction_of_CompletedFrickeData_of_PerNewformFullDirichletData
      h_fricke h_data
  exact strongMultiplicityOne_of_analyticContradiction_of_newformUnique
    h_unique h_ana f g χ hfχ hgχ S h

/-! ### T136 top-level classical-inputs consumers (corrected analytic route)

The corrected analytic route (T133/T134/T135) reduces `HeckeEntireExtension`
to two named classical analytic inputs:

* `Newform.HasFrickeTwistAsCuspForm` — Atkin-Lehner Fricke twist as a
  CuspForm-valued object plus slash equality (named H1a).
* `Newform.HasEulerStrippingMultiplier` — Euler-stripping multiplier with
  entirety and Dirichlet-series bridge (named H1b).

`Newform.HeckeEntireExtension_of_classicalInputs` already chains H1a + H1b
into the global `Newform.HeckeEntireExtension`.  This section provides the
three top-level consumers chaining the **classical inputs (H1a + H1b)** with
the existing T111 full Dirichlet-zero data block into the standard
analytic-route conclusions:

* `Newform.AnalyticContradiction`,
* `∃ q.Prime, q.Coprime N, q ∉ S, f.eigenvalue q ≠ 0` (the prime-nonvanishing
  conclusion needed for SMO),
* full Strong Multiplicity One (with `newform_unique`).

Each consumer is a pure composition of already-landed theorems (no new
analytic content; `Newform.HeckeEntireExtension_of_classicalInputs` for the
H1 side, and the existing
`*_of_HeckeEntireExtension_of_full_dirichletZeroCertificate*` consumers for
the H2 side).  Together they materially reduce the analytic route by naming
exactly the two classical Mellin/Fricke obligations plus the existing T111
Dirichlet-pole obligation, with no remaining opaque hypotheses.

References: Diamond–Shurman §5.9 Theorem 5.9.2; Miyake Theorem 4.5.16. -/

/-- **`Newform.AnalyticContradiction` from the two classical Mellin/Fricke
inputs plus the T111 full Dirichlet-zero data block (T136).**

Composes `Newform.HeckeEntireExtension_of_classicalInputs` (H1a + H1b ⇒
`HeckeEntireExtension`) with
`Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate`
(`HeckeEntireExtension` + full Dirichlet-zero data ⇒ `AnalyticContradiction`).
The resulting consumer names exactly the two Mellin/Fricke classical inputs
(`HasFrickeTwistAsCuspForm`, `HasEulerStrippingMultiplier`) plus the T111
full Dirichlet-zero data block, with no remaining opaque hypotheses. -/
theorem Newform.analyticContradiction_of_classicalInputs_of_full_dirichletZeroCertificate
    (h_fricke : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.HasFrickeTwistAsCuspForm f)
    (h_pos : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (_f : Newform N k), 0 < (k : ℝ))
    (h_stripping : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.HasEulerStrippingMultiplier f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
            (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹)) ≠ 0 ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) *
            (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹)) = 0 ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀) :
    Newform.AnalyticContradiction :=
  Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
    (Newform.HeckeEntireExtension_of_classicalInputs h_fricke h_pos h_stripping)
    h_data

/-- **Prime-nonvanishing eigenvalue from the two classical Mellin/Fricke
inputs plus the T111 full Dirichlet-zero data block (T136).**

Specialises
`Newform.analyticContradiction_of_classicalInputs_of_full_dirichletZeroCertificate`
through `Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction`
to the prime-nonvanishing conclusion needed by SMO.  This is the deepest
T136 consumer of the corrected analytic route: the analytic input is reduced
to the two named Mellin/Fricke classical predicates plus the existing T111
Dirichlet-pole certificate, with no remaining opaque content. -/
theorem Newform.exists_nonzero_prime_eigenvalue_of_classicalInputs_of_full_dirichletZeroCertificate
    (h_fricke : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.HasFrickeTwistAsCuspForm f)
    (h_pos : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (_f : Newform N k), 0 < (k : ℝ))
    (h_stripping : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.HasEulerStrippingMultiplier f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
            (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹)) ≠ 0 ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) *
            (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹)) = 0 ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀)
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, Nat.Coprime q N ∧ q ∉ S ∧
      f.eigenvalue ⟨q, hq.pos⟩ ≠ 0 :=
  Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction
    (Newform.analyticContradiction_of_classicalInputs_of_full_dirichletZeroCertificate
      h_fricke h_pos h_stripping h_data) f χ hfχ S

/-- **SMO endpoint: classical Mellin/Fricke inputs + full Dirichlet-zero
data + `newform_unique` (T136 endpoint).**

Top-level Strong Multiplicity One endpoint of the corrected analytic route:
combines the two named classical Mellin/Fricke inputs
(`HasFrickeTwistAsCuspForm`, `HasEulerStrippingMultiplier`) with the existing
T111 full Dirichlet-zero data block and `newform_unique`.  Replaces the older
`strongMultiplicityOne_of_FrickeSlashData_of_full_dirichletZeroCertificate_of_newformUnique`
(T132, false raw bridge) and
`strongMultiplicityOne_of_CompletedFrickeData_of_PerNewformFullDirichletData_of_newformUnique`
(T134, requires per-newform `CompletedFrickeData`) with the deepest reduction,
naming exactly the two classical analytic inputs. -/
theorem strongMultiplicityOne_of_classicalInputs_of_full_dirichletZeroCertificate_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_fricke : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.HasFrickeTwistAsCuspForm f)
    (h_pos : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (_f : Newform N k), 0 < (k : ℝ))
    (h_stripping : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.HasEulerStrippingMultiplier f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
            (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹)) ≠ 0 ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) *
            (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹)) = 0 ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm :=
  strongMultiplicityOne_of_HeckeEntireExtension_of_full_dirichletZeroCertificate_of_newformUnique
    h_unique
    (Newform.HeckeEntireExtension_of_classicalInputs h_fricke h_pos h_stripping)
    h_data f g χ hfχ hgχ S h

/-! ### End of corrected Fricke / completed Mellin data (T134) -/

/-! ### Level-raise preimage from supported q-expansion (T116)

For a cusp form `g : CuspForm Γ₁(N) k` whose period-1 `q`-expansion coefficients
vanish at every index that is not a multiple of `l` (with `1 < l`, `l ∣ N`),
the function `f(τ) := g ((levelRaiseMatrix l)⁻¹ • τ)` satisfies the two
hypotheses of `conductor_theorem_dichotomy_cuspForm_strong`:

* `⇑g = levelRaiseFun l k f` — direct by construction
  (inverse-action cancellation on `ℍ`).
* `f ∣[k] (mapGL ℝ ModularGroup.T) = f` — T-periodicity of `f` pulled back
  from a period-`1/l` periodicity of `g`, which follows from the Fourier
  support hypothesis via `hasSum_qExpansion` and the `l`-th-root-of-unity
  identity `exp(2πi · n) = 1` when `l ∣ n`.

This is **only** the function-level preimage plus T-periodicity; it is **not**
a modular-form / cusp-form descent and **not** a proof of `mainLemma`.
Combined with `conductor_theorem_dichotomy_cuspForm_strong` it yields the
descent of `g` to a `CuspForm` at level `Γ₁(N/l)` (Case A) or forces the
preimage function to vanish (Case B). -/

/-- The inverse level-raise action turns a unit `T`-translation upstairs into a
`(1/l)`-translation downstairs: `α_l⁻¹ • (1 +ᵥ τ) = (1/l) +ᵥ (α_l⁻¹ • τ)`. -/
private lemma levelRaiseMatrix_inv_smul_vadd_one_eq
    {l : ℕ} [NeZero l] (τ : UpperHalfPlane) :
    ((levelRaiseMatrix l)⁻¹ • ((1 : ℝ) +ᵥ τ) : UpperHalfPlane) =
      ((1 : ℝ) / (l : ℝ)) +ᵥ ((levelRaiseMatrix l)⁻¹ • τ) := by
  apply UpperHalfPlane.ext
  rw [coe_levelRaiseMatrix_inv_smul, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd,
    coe_levelRaiseMatrix_inv_smul]
  push_cast
  ring

/-- An `l`-th root of unity: `exp(2πi / l) ^ l = 1`. -/
private lemma exp_two_pi_mul_I_div_natCast_pow_eq_one (l : ℕ) [NeZero l] :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (l : ℂ)) ^ l = 1 := by
  have hl_ne : (l : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne l
  rw [← Complex.exp_nat_mul,
    show (l : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (l : ℂ)) =
        2 * (Real.pi : ℂ) * Complex.I from by field_simp]
  exact Complex.exp_two_pi_mul_I

/-- Term-wise invariance of the period-1 `q`-expansion summand under a
`(1/l)`-shift, given that the coefficients are supported on multiples of `l`.
The shifted `q`-parameter picks up a factor `exp(2πi / l)`; on a multiple of `l`
this is an `l`-th root of unity raised to a power (hence `1`), and off multiples
of `l` the coefficient vanishes. -/
private lemma qExpansion_coeff_smul_qParam_pow_shift_eq
    {N : ℕ} [NeZero N] {l : ℕ} [NeZero l] {k : ℤ}
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_supp : ∀ n : ℕ, ¬ l ∣ n →
      (ModularFormClass.qExpansion (1 : ℝ) g).coeff n = 0)
    (σ : UpperHalfPlane) (n : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ) g).coeff n •
        Function.Periodic.qParam (1 : ℝ)
          ((((1 : ℝ) / (l : ℝ)) +ᵥ σ : UpperHalfPlane) : ℂ) ^ n =
      (ModularFormClass.qExpansion (1 : ℝ) g).coeff n •
        Function.Periodic.qParam (1 : ℝ) (σ : ℂ) ^ n := by
  -- qParam 1 σ' = qParam 1 σ · exp(2πi/l), where σ' = (1/l) +ᵥ σ.
  have hqP :
      Function.Periodic.qParam (1 : ℝ) ((((1 : ℝ) / (l : ℝ)) +ᵥ σ : UpperHalfPlane) : ℂ) =
        Function.Periodic.qParam (1 : ℝ) (σ : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (l : ℂ)) := by
    have hσ'_eq : ((((1 : ℝ) / (l : ℝ)) +ᵥ σ : UpperHalfPlane) : ℂ) = (σ : ℂ) + 1 / (l : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    unfold Function.Periodic.qParam
    rw [hσ'_eq, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  by_cases hln : l ∣ n
  · -- l ∣ n: qParam^n is invariant since exp(2πi · m) = 1 for `n = l · m`.
    obtain ⟨m, rfl⟩ := hln
    rw [hqP, mul_pow,
      show Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (l : ℂ)) ^ (l * m) =
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (l : ℂ)) ^ l) ^ m from pow_mul _ l m,
      exp_two_pi_mul_I_div_natCast_pow_eq_one l, one_pow, mul_one]
  · -- ¬ l ∣ n: coeff = 0 by hypothesis.
    rw [hg_supp n hln, zero_smul, zero_smul]

theorem exists_levelRaise_preimage_of_coeff_support_multiples
    {N : ℕ} [NeZero N] {l : ℕ} [NeZero l] (_hl : 1 < l) (_hlN : l ∣ N) {k : ℤ}
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_supp : ∀ n : ℕ, ¬ l ∣ n →
      (ModularFormClass.qExpansion (1 : ℝ) g).coeff n = 0) :
    ∃ f : UpperHalfPlane → ℂ,
      (⇑g : UpperHalfPlane → ℂ) = levelRaiseFun l k f ∧
      f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f := by
  refine ⟨fun τ => (⇑g : _ → ℂ) ((levelRaiseMatrix l)⁻¹ • τ), ?_, ?_⟩
  · -- Part 1: ⇑g = levelRaiseFun l k f.
    funext τ
    show (⇑g : _ → ℂ) τ = levelRaiseFun l k _ τ
    rw [levelRaiseFun_apply]
    show (⇑g : _ → ℂ) τ =
      (⇑g : _ → ℂ) ((levelRaiseMatrix l)⁻¹ • (levelRaiseMatrix l • τ))
    rw [← mul_smul, inv_mul_cancel, one_smul]
  · -- Part 2: f ∣[k] (mapGL ℝ T) = f, via fractional-period argument on `g`.
    have h1_pos : (0 : ℝ) < 1 := one_pos
    have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
      rw [show (Gamma1 N).map (mapGL ℝ) =
            (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
        CongruenceSubgroup.strictPeriods_Gamma1]
      exact ⟨1, by simp⟩
    -- The slash at `mapGL T` reduces to translation by 1 (SL slash = GL slash
    -- definitionally since `SLAction` is `monoidHomSlashAction (mapGL ℝ)`).
    funext τ
    show ((fun τ' => (⇑g : _ → ℂ) ((levelRaiseMatrix l)⁻¹ • τ')) ∣[k]
        (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ)) τ =
        (⇑g : _ → ℂ) ((levelRaiseMatrix l)⁻¹ • τ)
    rw [show ((fun τ' => (⇑g : _ → ℂ) ((levelRaiseMatrix l)⁻¹ • τ')) ∣[k]
          (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ)) =
        ((fun τ' => (⇑g : _ → ℂ) ((levelRaiseMatrix l)⁻¹ • τ')) ∣[k]
          (ModularGroup.T : SL(2, ℤ))) from rfl,
      modular_slash_T_apply]
    -- Goal: g ((levelRaiseMatrix l)⁻¹ • (1 +ᵥ τ)) = g ((levelRaiseMatrix l)⁻¹ • τ).
    -- Set σ := (levelRaiseMatrix l)⁻¹ • τ and rewrite the LHS action to a
    -- `(1/l)`-shift of σ (`levelRaiseMatrix_inv_smul_vadd_one_eq`), reducing to
    -- `g σ' = g σ`.
    set σ : UpperHalfPlane := (levelRaiseMatrix l)⁻¹ • τ
    rw [levelRaiseMatrix_inv_smul_vadd_one_eq τ]
    set σ' : UpperHalfPlane := ((1 : ℝ) / (l : ℝ)) +ᵥ σ
    -- Compare the period-1 `q`-expansions at σ and σ' term-by-term: both have
    -- the same summand sequence (`qExpansion_coeff_smul_qParam_pow_shift_eq`),
    -- so `g σ' = g σ` by uniqueness of the `HasSum` limit.
    have Hσ : HasSum (fun n : ℕ =>
        (ModularFormClass.qExpansion (1 : ℝ) g).coeff n •
          Function.Periodic.qParam (1 : ℝ) (σ : ℂ) ^ n) ((⇑g : _ → ℂ) σ) :=
      ModularFormClass.hasSum_qExpansion (f := g) h1_pos h1_period σ
    have Hσ' : HasSum (fun n : ℕ =>
        (ModularFormClass.qExpansion (1 : ℝ) g).coeff n •
          Function.Periodic.qParam (1 : ℝ) (σ' : ℂ) ^ n) ((⇑g : _ → ℂ) σ') :=
      ModularFormClass.hasSum_qExpansion (f := g) h1_pos h1_period σ'
    rw [funext (qExpansion_coeff_smul_qParam_pow_shift_eq g hg_supp σ)] at Hσ'
    exact (Hσ.unique Hσ').symm

/-! ### Conditional Strong Multiplicity One from the newSubspace zero criterion -/

/-- **Conditional Strong Multiplicity One from the newSubspace zero criterion
plus the analytic-contradiction hypothesis.**

Combines `newform_unique_of_newSubspace_coprime_vanishing_zero` (PROVED) with
`Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction` (PROVED)
to give the Strong Multiplicity One conclusion.

The hypothesis `h_zero` is the exact same conditional handoff used by
`mainLemma_of_newSubspace_coprime_vanishing_zero` (and is what the Hecke
adjoint / eigenbasis lane is meant to supply via `T205-d` + `T207`).  The
hypothesis `h_ana` is `Newform.AnalyticContradiction`, the named analytic
obligation of T132.

This is the lowest-level conditional formulation of SMO available: both
hypotheses are precisely the two genuine remaining obligations
(spectral/adjoint + analytic L-functions) for unconditional closure. -/
theorem strongMultiplicityOne_of_analyticContradiction_of_newSubspaceZeroCriterion
    (h_zero : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄
      (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      g ∈ cuspFormsNew N k →
      (∀ n : ℕ, Nat.Coprime n N →
        (ModularFormClass.qExpansion (1 : ℝ) g).coeff n = 0) →
      g = 0)
    (h_ana : Newform.AnalyticContradiction)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  refine newform_unique_of_newSubspace_coprime_vanishing_zero
    (@h_zero N _ k) f g χ hfχ hgχ ?_
  intro n hn
  by_cases hn_S : n.val ∈ S
  · have hn_pos : 0 < n.val := n.pos
    let bad : Finset ℕ := S ∪ S.image (· / n.val) ∪ n.val.primeFactors
    obtain ⟨q, hq_prime, hq_N, hq_notin, hq_ne⟩ :=
      Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction
        h_ana f χ hfχ bad
    have hq_pos : 0 < q := hq_prime.pos
    have hq_notin_S : q ∉ S := fun hqS => hq_notin (by
      simp only [bad, Finset.mem_union]; exact Or.inl (Or.inl hqS))
    have hq_notin_img : q ∉ S.image (· / n.val) := fun h' => hq_notin (by
      simp only [bad, Finset.mem_union]; exact Or.inl (Or.inr h'))
    have hq_nd_n : ¬ q ∣ n.val := fun hqn => hq_notin (by
      simp only [bad, Finset.mem_union, Nat.mem_primeFactors]
      exact Or.inr ⟨hq_prime, hqn, hn_pos.ne'⟩)
    have hn_coprime_q : Nat.Coprime n.val q :=
      ((hq_prime.coprime_iff_not_dvd).mpr hq_nd_n).symm
    have hnq_notin_S : n.val * q ∉ S := fun hnqS => hq_notin_img <| by
      refine Finset.mem_image.mpr ⟨n.val * q, hnqS, ?_⟩
      exact Nat.mul_div_cancel_left _ hn_pos
    let q_pnat : ℕ+ := ⟨q, hq_pos⟩
    let nq_pnat : ℕ+ := ⟨n.val * q, Nat.mul_pos hn_pos hq_pos⟩
    have hnq_N : Nat.Coprime (n.val * q) N := hn.mul_left hq_N
    have hq_eq : f.eigenvalue q_pnat = g.eigenvalue q_pnat := h q_pnat hq_N hq_notin_S
    have hnq_eq : f.eigenvalue nq_pnat = g.eigenvalue nq_pnat := h nq_pnat hnq_N hnq_notin_S
    have hmul_f : f.eigenvalue nq_pnat = f.eigenvalue n * f.eigenvalue q_pnat :=
      Newform.eigenvalue_coprime_mul f n q_pnat hn hq_N hn_coprime_q χ hfχ
    have hmul_g : g.eigenvalue nq_pnat = g.eigenvalue n * g.eigenvalue q_pnat :=
      Newform.eigenvalue_coprime_mul g n q_pnat hn hq_N hn_coprime_q χ hgχ
    have hcomb :
        f.eigenvalue n * f.eigenvalue q_pnat = g.eigenvalue n * f.eigenvalue q_pnat := by
      rw [← hmul_f, hnq_eq, hmul_g, hq_eq]
    exact mul_right_cancel₀ hq_ne hcomb
  · exact h n hn hn_S

end HeckeRing.GL2
