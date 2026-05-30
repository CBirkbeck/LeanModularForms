/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.EMetricSpace.Paracompact

@[expose] public section

/-!
# Miscellaneous `Tendsto` lemmas

Auxiliary `Tendsto` reindexing lemmas (`ℤ` / `ℕ` / `ℕ+`) and a perturbation lemma used
internally by the modular-forms development.
-/

open Filter Topology

private lemma int_tendsto_nat {f : ℤ → ℂ} {x : ℂ} (hf : Tendsto f atTop (𝓝 x)) :
    Tendsto (fun n : ℕ ↦ f n) atTop (𝓝 x) :=
  hf.comp tendsto_natCast_atTop_atTop

private lemma pnat_tendsto_nat (f : ℕ → ℂ) (x : ℂ)
    (hf : Tendsto (fun n : ℕ+ ↦ f n) atTop (𝓝 x)) : Tendsto f atTop (𝓝 x) :=
  tendsto_comp_val_Ioi_atTop.mp hf

private lemma nat_tendsto_pnat (f : ℕ → ℂ) (x : ℂ) (hf : Tendsto f atTop (𝓝 x)) :
    Tendsto (fun n : ℕ+ ↦ f n) atTop (𝓝 x) :=
  tendsto_comp_val_Ioi_atTop.mpr hf

private lemma tendsto_of_sub_tendsto_zero (f g : ℕ → ℂ) (x : ℂ)
    (hf : Tendsto f atTop (𝓝 x)) (hfg : Tendsto (g - f) atTop (𝓝 0)) :
    Tendsto g atTop (𝓝 x) := by
  simpa using hf.add hfg

private lemma tendsto_one_sub_pow (r : ℂ) (hr : ‖r‖ < 1) :
    Tendsto (fun n : ℕ ↦ 1 - r ^ n) atTop (𝓝 1) := by
  simpa using tendsto_const_nhds.sub <| tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr
