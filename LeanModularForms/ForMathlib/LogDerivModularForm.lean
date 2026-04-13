/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.MeromorphicBridge
import LeanModularForms.ForMathlib.Residue
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Properties of the Logarithmic Derivative of a Meromorphic Function

This file establishes key properties of `logDeriv f = f'/f` when `f` is meromorphic,
needed by the valence formula.

## Main results

* `logDeriv_hasSimplePoleAt_of_order` -- if `f` has meromorphic order `n ≠ 0` at `z₀`,
  then `logDeriv f` has a simple pole at `z₀` with coefficient `↑n`.
* `logDeriv_residue_eq_order` -- the residue of `logDeriv f` at `z₀` equals the
  meromorphic order `(meromorphicOrderAt f z₀).untop₀`.
* `logDeriv_periodic` -- if `f(z + c) = f(z)` for all `z`, then
  `logDeriv f (z + c) = logDeriv f z`.

## Proof strategy

The core argument: if `meromorphicOrderAt f z₀ = n` (finite), Mathlib's factorization
gives `f =ᶠ[𝓝[≠] z₀] (z - z₀)^n • g(z)` with `g` analytic and `g(z₀) ≠ 0`. Then
near `z₀` (at points `z ≠ z₀`):

  `logDeriv f z = n / (z - z₀) + logDeriv g z`

where `logDeriv g` is analytic at `z₀` (since `g` is analytic and nonvanishing there).
This is a simple pole decomposition with coefficient `↑n`, from which the residue
follows immediately.

For periodicity, the key identity is `deriv (f ∘ (· + c)) = deriv f ∘ (· + c)`, which
combined with `f(z + c) = f(z)` gives `logDeriv f (z + c) = logDeriv f z`.

## References

* A. Knapp, *Elliptic Curves*, Chapter V
* J.-P. Serre, *A Course in Arithmetic*, Chapter VII
-/

open Complex Set Filter Topology

noncomputable section

/-! ### Helpers -/

/-- From `f =ᶠ[𝓝[≠] z₀] g`, deduce that for each `z` in the punctured neighborhood,
`f =ᶠ[𝓝 z] g` (i.e., `f` and `g` agree on a full neighborhood of `z`). This holds
because the punctured neighborhood contains an open set minus `{z₀}`, and at any
`z ≠ z₀` in this set, a ball around `z` avoiding `z₀` lies inside the set. -/
private lemma nhdsNE_eventuallyEq_to_nhds {z₀ : ℂ} {f g : ℂ → ℂ}
    (hfg : f =ᶠ[𝓝[≠] z₀] g) :
    ∀ᶠ z in 𝓝[≠] z₀, f =ᶠ[𝓝 z] g := by
  obtain ⟨s, hs_open, hs_mem, hs_sub⟩ := mem_nhdsWithin.mp hfg
  refine mem_nhdsWithin.mpr ⟨s, hs_open, hs_mem, ?_⟩
  intro z ⟨hz_s, hz_ne⟩
  exact Filter.mem_of_superset (Filter.inter_mem (hs_open.mem_nhds hz_s)
    (isOpen_compl_singleton.mem_nhds (mem_compl_singleton_iff.mpr hz_ne)))
    fun w ⟨hw_s, hw_ne⟩ => hs_sub ⟨hw_s, hw_ne⟩

/-- The logarithmic derivative of `(z - z₀)^n * g(z)` at a point `z ≠ z₀` with `g z ≠ 0`
equals `n / (z - z₀) + logDeriv g z`.

The proof uses the product rule for derivatives and algebraic simplification. -/
private lemma logDeriv_zpow_mul_eq {z₀ z : ℂ} {n : ℤ} {g : ℂ → ℂ}
    (hzsub : z - z₀ ≠ 0) (hgz_ne : g z ≠ 0) (hgz_diff : DifferentiableAt ℂ g z) :
    logDeriv (fun w => (w - z₀) ^ n * g w) z = ↑n / (z - z₀) + logDeriv g z := by
  simp only [logDeriv_apply]
  have h_sub : HasDerivAt (· - z₀) 1 z := by
    have h := (hasDerivAt_id z).sub (hasDerivAt_const z z₀); rwa [sub_zero] at h
  have h_zpow : HasDerivAt (fun w => (w - z₀) ^ n) (↑n * (z - z₀) ^ (n - 1)) z := by
    simpa using (hasDerivAt_zpow n _ (Or.inl hzsub)).comp z h_sub
  have hderiv : deriv (fun w => (w - z₀) ^ n * g w) z =
      ↑n * (z - z₀) ^ (n - 1) * g z + (z - z₀) ^ n * deriv g z := by
    rw [show (fun w => (w - z₀) ^ n * g w) = (fun w => (w - z₀) ^ n) * g from rfl,
      (h_zpow.mul hgz_diff.hasDerivAt).deriv]
  rw [hderiv, add_div, mul_div_mul_right _ _ hgz_ne,
    mul_div_mul_left _ _ (zpow_ne_zero n hzsub), zpow_sub_one₀ hzsub n]
  field_simp

/-- The logarithmic derivative of `f` has a simple pole decomposition
`logDeriv f z = ↑n / (z - z₀) + logDeriv g z` near `z₀`, given the Mathlib
meromorphic factorization `f =ᶠ (z - z₀)^n • g` with `g` analytic, `g(z₀) ≠ 0`. -/
private lemma logDeriv_eventually_eq_pole_decomp {f : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    {g : ℂ → ℂ} (hg_an : AnalyticAt ℂ g z₀) (hg_ne : g z₀ ≠ 0)
    (hg_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ n • g z) :
    ∀ᶠ z in 𝓝[≠] z₀, logDeriv f z = ↑n / (z - z₀) + logDeriv g z := by
  have hfmul : f =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ n * g z :=
    hg_eq.mono fun z hz => by rw [hz, smul_eq_mul]
  have hfmul_nhds := nhdsNE_eventuallyEq_to_nhds hfmul
  have hg_ne_near : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 := hg_an.continuousAt.eventually_ne hg_ne
  have hg_diff : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g z :=
    hg_an.eventually_analyticAt.mono fun z hz => hz.differentiableAt
  filter_upwards [hfmul_nhds, hg_ne_near.filter_mono nhdsWithin_le_nhds,
    hg_diff.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with z hfz_nhds hgz_ne hgz_diff hne
  have hzsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hne
  rw [show logDeriv f z = logDeriv (fun w => (w - z₀) ^ n * g w) z from by
    simp only [logDeriv_apply, hfz_nhds.deriv_eq, hfz_nhds.self_of_nhds]]
  exact logDeriv_zpow_mul_eq hzsub hgz_ne hgz_diff

/-! ### Simple pole structure of `logDeriv` -/

/-- If `f` is meromorphic at `z₀` with finite nonzero order `n`, then `logDeriv f` has a
simple pole at `z₀` with coefficient `↑n`.

From the meromorphic factorization `f =ᶠ (z - z₀)^n • g` with `g` analytic and
`g(z₀) ≠ 0`, we get `logDeriv f z = n/(z - z₀) + logDeriv g z` near `z₀`, which is
a simple pole decomposition since `logDeriv g` is analytic at `z₀`. -/
theorem logDeriv_hasSimplePoleAt_of_order {f : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    (hf : MeromorphicAt f z₀)
    (hord : meromorphicOrderAt f z₀ = (n : ℤ)) (_hn : n ≠ 0) :
    HasSimplePoleAt (logDeriv f) z₀ := by
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord
  exact ⟨↑n, logDeriv g, hg_an.deriv.fun_div hg_an hg_ne,
    logDeriv_eventually_eq_pole_decomp hg_an hg_ne hg_eq⟩

/-! ### Residue of `logDeriv` equals the meromorphic order -/

/-- The residue of `logDeriv f` at `z₀` equals the meromorphic order of `f` at `z₀`.

More precisely, `residue (logDeriv f) z₀ = ↑(meromorphicOrderAt f z₀).untop₀`. When
the order is `n ∈ ℤ`, this is just `↑n`. The proof constructs the explicit simple pole
decomposition `logDeriv f = n/(z - z₀) + logDeriv g` and applies
`residue_eq_of_simple_pole_decomp`. -/
theorem logDeriv_residue_eq_order {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : MeromorphicAt f z₀) (hord : meromorphicOrderAt f z₀ ≠ ⊤) :
    residue (logDeriv f) z₀ = ↑(meromorphicOrderAt f z₀).untop₀ := by
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_ne_top_iff hf).mp hord
  exact residue_eq_of_simple_pole_decomp (hg_an.deriv.fun_div hg_an hg_ne)
    (logDeriv_eventually_eq_pole_decomp hg_an hg_ne hg_eq)

/-- Variant of `logDeriv_residue_eq_order` with the order given as a concrete integer. -/
theorem logDeriv_residue_eq_int {f : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    (hf : MeromorphicAt f z₀)
    (hord : meromorphicOrderAt f z₀ = (n : ℤ)) :
    residue (logDeriv f) z₀ = ↑n := by
  have hne : meromorphicOrderAt f z₀ ≠ ⊤ := by rw [hord]; exact WithTop.coe_ne_top
  rw [logDeriv_residue_eq_order hf hne, hord]
  simp

/-! ### Periodicity of `logDeriv` -/

/-- If `f` is periodic with period `c` (i.e., `f(z + c) = f(z)` for all `z`), then
`logDeriv f` is also periodic with period `c`.

The proof uses that `deriv (f ∘ (· + c)) z = deriv f (z + c)` (translation invariance
of the derivative) together with `f = f ∘ (· + c)` (periodicity). -/
theorem logDeriv_periodic {f : ℂ → ℂ} {c : ℂ} (hf : ∀ z, f (z + c) = f z) :
    ∀ z, logDeriv f (z + c) = logDeriv f z := by
  intro z
  simp only [logDeriv_apply, ← deriv_comp_add_const f c z,
    show (fun w => f (w + c)) = f from funext hf, hf z]

/-- Specialization: if `f(z + 1) = f(z)` for all `z`, then `logDeriv f (z + 1) = logDeriv f z`.
This is the key periodicity used for modular forms of level 1. -/
theorem logDeriv_periodic_one {f : ℂ → ℂ} (hf : ∀ z, f (z + (1 : ℂ)) = f z) :
    ∀ z, logDeriv f (z + 1) = logDeriv f z :=
  logDeriv_periodic hf

end
