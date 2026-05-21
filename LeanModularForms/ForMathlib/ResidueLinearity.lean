/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.ResidueCircleIntegral

/-!
# Residue calculus: linearity

Basic linearity properties of `residue` for functions with simple poles.

The key bridge is `residue_eq_coeff`: when `f` has a simple pole at `z₀`, its
residue equals the pole coefficient extracted via `HasSimplePoleAt.coeff`. So
linearity of residues reduces to linearity of coefficients of the simple-pole
decomposition `f(z) = c/(z-z₀) + g(z)`.

## Main results

* `HasSimplePoleAt.add` — `f + g` has a simple pole with coeff `cf + cg`.
* `HasSimplePoleAt.sub` — `f - g` has a simple pole with coeff `cf - cg`.
* `HasSimplePoleAt.const_smul` — `c * f` has a simple pole with coeff `c * cf`.
* `HasSimplePoleAt.finset_sum` — finite sums.

* `residue_add` — `Res(f + g) = Res(f) + Res(g)`.
* `residue_sub` — `Res(f - g) = Res(f) - Res(g)`.
* `residue_const_smul` — `Res(c · f) = c · Res(f)`.
* `residue_finset_sum` — finite-sum linearity.
* `residue_const_div_sub` — `Res(c/(z-s)) = c`.
-/

open Complex Set Filter Topology

noncomputable section

namespace HasSimplePoleAt

variable {f g : ℂ → ℂ} {z₀ : ℂ}

/-- The sum of two functions with simple poles at `z₀` has a simple pole at `z₀`
with coefficient `hf.coeff + hg.coeff`. -/
theorem add (hf : HasSimplePoleAt f z₀) (hg : HasSimplePoleAt g z₀) :
    HasSimplePoleAt (fun z => f z + g z) z₀ := by
  refine ⟨hf.coeff + hg.coeff, fun z => hf.regularPart z + hg.regularPart z,
    hf.regularPart_analyticAt.add hg.regularPart_analyticAt, ?_⟩
  filter_upwards [hf.eventually_eq, hg.eventually_eq] with z hfe hge
  rw [hfe, hge]; ring

/-- The difference of two functions with simple poles at `z₀` has a simple pole at `z₀`
with coefficient `hf.coeff - hg.coeff`. -/
theorem sub (hf : HasSimplePoleAt f z₀) (hg : HasSimplePoleAt g z₀) :
    HasSimplePoleAt (fun z => f z - g z) z₀ := by
  refine ⟨hf.coeff - hg.coeff, fun z => hf.regularPart z - hg.regularPart z,
    hf.regularPart_analyticAt.sub hg.regularPart_analyticAt, ?_⟩
  filter_upwards [hf.eventually_eq, hg.eventually_eq] with z hfe hge
  rw [hfe, hge]; ring

/-- Multiplication by a constant preserves simple-pole structure: `c · f` has a
simple pole at `z₀` with coefficient `c * hf.coeff`. -/
theorem const_mul (c : ℂ) (hf : HasSimplePoleAt f z₀) :
    HasSimplePoleAt (fun z => c * f z) z₀ := by
  refine ⟨c * hf.coeff, fun z => c * hf.regularPart z,
    analyticAt_const.mul hf.regularPart_analyticAt, ?_⟩
  filter_upwards [hf.eventually_eq] with z hfe
  rw [hfe]; ring

/-- A finite sum of functions, each with a simple pole at `z₀`, has a simple pole
at `z₀`. -/
theorem finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ℂ → ℂ) (z₀ : ℂ)
    (hF : ∀ i ∈ s, HasSimplePoleAt (F i) z₀) :
    HasSimplePoleAt (fun z => ∑ i ∈ s, F i z) z₀ := by
  induction s using Finset.induction with
  | empty =>
    -- The empty sum is the zero function; analytic, hence trivial simple pole.
    refine ⟨0, fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards with z
    simp
  | insert i s hi_notin ih =>
    have hi_simple : HasSimplePoleAt (F i) z₀ := hF i (Finset.mem_insert_self _ _)
    have hs_simple : HasSimplePoleAt (fun z => ∑ j ∈ s, F j z) z₀ :=
      ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    obtain ⟨c, g, hg_analytic, hg_eq⟩ := hi_simple.add hs_simple
    refine ⟨c, g, hg_analytic, ?_⟩
    filter_upwards [hg_eq] with z hz
    rw [Finset.sum_insert hi_notin]
    exact hz

end HasSimplePoleAt

/-- The residue of a sum equals the sum of residues, for functions with simple poles. -/
theorem residue_add {f g : ℂ → ℂ} {z₀ : ℂ}
    (hf : HasSimplePoleAt f z₀) (hg : HasSimplePoleAt g z₀) :
    residue (fun z => f z + g z) z₀ = residue f z₀ + residue g z₀ := by
  have h_eq : residue (fun z => f z + g z) z₀ = hf.coeff + hg.coeff :=
    residue_eq_of_simple_pole_decomp
      (c := hf.coeff + hg.coeff)
      (g := fun z => hf.regularPart z + hg.regularPart z)
      (hf.regularPart_analyticAt.add hg.regularPart_analyticAt)
      (by
        filter_upwards [hf.eventually_eq, hg.eventually_eq] with z hfe hge
        rw [hfe, hge]; ring)
  rw [h_eq, residue_eq_coeff hf, residue_eq_coeff hg]

/-- The residue of a difference equals the difference of residues, for functions
with simple poles. -/
theorem residue_sub {f g : ℂ → ℂ} {z₀ : ℂ}
    (hf : HasSimplePoleAt f z₀) (hg : HasSimplePoleAt g z₀) :
    residue (fun z => f z - g z) z₀ = residue f z₀ - residue g z₀ := by
  have h_eq : residue (fun z => f z - g z) z₀ = hf.coeff - hg.coeff :=
    residue_eq_of_simple_pole_decomp
      (c := hf.coeff - hg.coeff)
      (g := fun z => hf.regularPart z - hg.regularPart z)
      (hf.regularPart_analyticAt.sub hg.regularPart_analyticAt)
      (by
        filter_upwards [hf.eventually_eq, hg.eventually_eq] with z hfe hge
        rw [hfe, hge]; ring)
  rw [h_eq, residue_eq_coeff hf, residue_eq_coeff hg]

/-- Residue is homogeneous under multiplication by a constant. -/
theorem residue_const_mul {f : ℂ → ℂ} (c : ℂ) {z₀ : ℂ}
    (hf : HasSimplePoleAt f z₀) :
    residue (fun z => c * f z) z₀ = c * residue f z₀ := by
  have h_eq : residue (fun z => c * f z) z₀ = c * hf.coeff :=
    residue_eq_of_simple_pole_decomp
      (c := c * hf.coeff)
      (g := fun z => c * hf.regularPart z)
      (analyticAt_const.mul hf.regularPart_analyticAt)
      (by
        filter_upwards [hf.eventually_eq] with z hfe
        rw [hfe]; ring)
  rw [h_eq, residue_eq_coeff hf]

/-- Alias spelled `residue_const_smul` (compatible with the `c • f` reading). -/
theorem residue_const_smul {f : ℂ → ℂ} (c : ℂ) {z₀ : ℂ}
    (hf : HasSimplePoleAt f z₀) :
    residue (fun z => c * f z) z₀ = c * residue f z₀ :=
  residue_const_mul c hf

/-- The residue of `c/(z - s)` at `s` equals `c`. -/
theorem residue_const_div_sub (c s : ℂ) :
    residue (fun z => c / (z - s)) s = c := by
  -- Decompose `c/(z-s) = c/(z-s) + 0`, with `0` analytic. The hypothesis is
  -- definitionally trivial on the punctured neighborhood.
  refine residue_eq_of_simple_pole_decomp (g := fun _ => (0 : ℂ)) analyticAt_const ?_
  filter_upwards with z
  simp

/-- The residue of a finite sum equals the sum of residues, for functions each
with a simple pole at `z₀`. -/
theorem residue_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ℂ → ℂ) (z₀ : ℂ)
    (hF : ∀ i ∈ s, HasSimplePoleAt (F i) z₀) :
    residue (fun z => ∑ i ∈ s, F i z) z₀ = ∑ i ∈ s, residue (F i) z₀ := by
  induction s using Finset.induction with
  | empty =>
    -- Empty sum: residue of the zero function is `0` (analytic).
    simp only [Finset.sum_empty]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  | insert i s hi_notin ih =>
    have hi_simple : HasSimplePoleAt (F i) z₀ := hF i (Finset.mem_insert_self _ _)
    have hs_simple : HasSimplePoleAt (fun z => ∑ j ∈ s, F j z) z₀ :=
      HasSimplePoleAt.finset_sum s F z₀
        (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    have ih' : residue (fun z => ∑ j ∈ s, F j z) z₀ = ∑ j ∈ s, residue (F j) z₀ :=
      ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    -- Express insert-sum as `F i z + (∑ over s)` via `residue_congr`.
    have h_eq : residue (fun z => ∑ j ∈ insert i s, F j z) z₀ =
        residue (fun z => F i z + ∑ j ∈ s, F j z) z₀ := by
      apply residue_congr
      filter_upwards with z
      simp [Finset.sum_insert hi_notin]
    rw [h_eq, residue_add hi_simple hs_simple, ih', Finset.sum_insert hi_notin]

end
