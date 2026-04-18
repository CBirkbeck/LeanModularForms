/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Prop334_HeckeSlashDiag

/-!
# Explicit Hecke slash for `D_p_Gamma0` and functional χ-equivariance

This file implements the Shimura/Diamond–Shurman explicit-rep approach to the
functional χ-equivariance of the Hecke operator on `modFormCharSpace k χ` at
the `D_p_Gamma0 N p` double coset (for `p` prime coprime to `N`).

## Strategy

The existing `heckeSlash_gen` definition (in `HeckeActionGeneral.lean`) sums
over `decompQuot` classes using `Quotient.out` to pick representatives. For a
χ-eigenform `f` with non-trivial `χ`, this `.out`-based rep selection makes the
per-term χ-factors dependent on `Classical.choice` noise, obstructing a uniform
functional χ-equivariance proof at the abstract level.

The **explicit** approach picks the `p+1` classical Shimura coset reps
`{T_p_upper(b) : b ∈ Fin p} ∪ {T_p_lower}` and works with
`heckeT_p_fun` (which already carries the correct `⟨p⟩`-twist on the
`T_p_lower` term) rather than the abstract sum. At this level, the
χ-equivariance is `heckeT_p_fun_slash_comm_charSpace` (proved in
`Prop334_HeckeSlashDiag.lean`).

The bridge from `heckeSlash_gen` to `heckeT_p_fun` is:
* For `χ = 1` (trivial character):
  `heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one` gives the
  unconditional equality.
* For general `χ`: the bridge is more delicate because the `.out`-rep
  χ-factors do not uniformly simplify. The existing conditional statement
  `heckeSlash_gen_functional_equivariance_D_p_Gamma0_of_bridge` packages the
  bridge hypothesis explicitly; downstream consumers that can verify the
  bridge obtain the functional χ-equivariance via this conditional.

## Main results

* `heckeSlash_explicit_D_p_Gamma0` — noncomputable def: the explicit Hecke
  slash, definitionally `heckeT_p_fun`.
* `heckeSlash_explicit_D_p_Gamma0_eq_heckeT_p_fun` — definitional identity
  relating the explicit sum (with `⟨p⟩`-twist) to `heckeT_p_fun`.
* `heckeSlash_explicit_D_p_Gamma0_expand` — the explicit Hecke slash expanded
  as `heckeT_p_ut (⇑f) + (⟨p⟩ f) ∣[k] T_p_lower`.
* `heckeT_p_fun_functional_equivariance_D_p_Gamma0` — functional
  χ-equivariance of `heckeT_p_fun` (a direct wrapping of
  `heckeT_p_fun_slash_comm_charSpace`).
* `heckeSlash_explicit_D_p_Gamma0_functional_equivariance` — functional
  χ-equivariance of the explicit Hecke slash.
* `M_infty_mem_D_p_Gamma0` — membership of `M_∞` in the Γ₀-level double
  coset `D_p_Gamma0 N p hp.pos`, leveraged in the general-χ bridge argument.
* `heckeSlash_gen_eq_heckeT_p_fun_charSpace_one` — bridge at `χ = 1`,
  reformulated in the conditional bridge form of
  `heckeSlash_gen_functional_equivariance_D_p_Gamma0_of_bridge`.
* `heckeSlash_gen_functional_equivariance_D_p_Gamma0_trivial_via_explicit` —
  alternative derivation of the trivial-χ case through the explicit path.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing DoubleCoset

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-! ### The explicit Hecke slash operator at `D_p_Gamma0`

The explicit form of the Hecke operator on `modFormCharSpace k χ` at the
`D_p_Gamma0 N p` double coset uses the Shimura coset reps
`{T_p_upper(b) : b ∈ Fin p} ∪ {T_p_lower}`, with the canonical `⟨p⟩`-twist
on the `T_p_lower` term (Diamond–Shurman Prop 5.2.1). This coincides with
`heckeT_p_fun` by definition. -/

/-- The explicit Hecke slash operator at `D_p_Gamma0 N p hp`, which is
definitionally equal to `heckeT_p_fun k p hp hpN f`.

This is the sum `Σ_{b < p} f ∣[k] T_p_upper(b) + (⟨p⟩ f) ∣[k] T_p_lower`,
exactly matching the Diamond–Shurman `T_p` formula on `ModularForm`. -/
noncomputable def heckeSlash_explicit_D_p_Gamma0 (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    UpperHalfPlane → ℂ :=
  heckeT_p_fun k p hp hpN f

/-- **Definitional bridge**: `heckeSlash_explicit_D_p_Gamma0 = heckeT_p_fun`. -/
lemma heckeSlash_explicit_D_p_Gamma0_eq_heckeT_p_fun (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeSlash_explicit_D_p_Gamma0 k p hp hpN f =
    heckeT_p_fun k p hp hpN f := rfl

/-- **Expansion**: the explicit Hecke slash equals
`heckeT_p_ut k p hp.pos (⇑f) + (⟨p⟩ f) ∣[k] T_p_lower`, i.e. the Diamond–Shurman
explicit `T_p` formula. -/
lemma heckeSlash_explicit_D_p_Gamma0_expand (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeSlash_explicit_D_p_Gamma0 k p hp hpN f =
    heckeT_p_ut k p hp.pos (⇑f) +
      (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) := rfl

/-! ### Functional χ-equivariance (at the `heckeT_p_fun` level)

For `f ∈ modFormCharSpace k χ`, the Hecke operator `heckeT_p_fun` (i.e.
`heckeSlash_explicit_D_p_Gamma0`) satisfies the functional χ-equivariance
for the `Γ₀(N)`-slash action. This is a direct restatement of
`heckeT_p_fun_slash_comm_charSpace`. -/

/-- **Functional χ-equivariance of `heckeT_p_fun`**: for `f ∈ modFormCharSpace k χ`
and `g ∈ Γ₀(N)`,
```
heckeT_p_fun k p hp hpN f ∣[k] mapGL ℝ g = χ(Gamma0MapUnits g) • heckeT_p_fun k p hp hpN f
```
This is precisely `heckeT_p_fun_slash_comm_charSpace`, restated in the
`heckeSlash_gen_functional_equivariance_D_p_Gamma0`-compatible form. -/
theorem heckeT_p_fun_functional_equivariance_D_p_Gamma0
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ)
    (g : ↥(Gamma0 N)) :
    heckeT_p_fun k p hp hpN f ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
    (↑(χ (Gamma0MapUnits g)) : ℂ) • heckeT_p_fun k p hp hpN f :=
  heckeT_p_fun_slash_comm_charSpace k p hp hpN χ hf g

/-- **Functional χ-equivariance of the explicit Hecke slash**: direct from
the definitional identity and `heckeT_p_fun_functional_equivariance_D_p_Gamma0`. -/
theorem heckeSlash_explicit_D_p_Gamma0_functional_equivariance
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ)
    (g : ↥(Gamma0 N)) :
    heckeSlash_explicit_D_p_Gamma0 k p hp hpN f ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
    (↑(χ (Gamma0MapUnits g)) : ℂ) •
      heckeSlash_explicit_D_p_Gamma0 k p hp hpN f :=
  heckeT_p_fun_functional_equivariance_D_p_Gamma0 k χ p hp hpN hf g

/-! ### Bridge: `heckeSlash_gen D_p_Gamma0 ⇑f = heckeT_p_fun f`

For `f ∈ modFormCharSpace k χ`, the conditional
`heckeSlash_gen_functional_equivariance_D_p_Gamma0_of_bridge` requires the
hypothesis `heckeSlash_gen D_p_Gamma0 ⇑f = heckeT_p_fun f`.

At `χ = 1`, this bridge is **unconditional** via
`heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one`.

For general `χ`, the bridge relates the abstract `.out`-rep sum to the
explicit `T_p` formula; see the classical Diamond–Shurman Prop 5.2.1 analysis.

The explicit-rep matching
`tRep_gen_D_p_Gamma0_matches_T_p_reps` gives, for a `Γ₀(N)`-invariant `f`:
```
Σ_σ f ∣[k] tRep_gen σ = Σ_b f ∣[k] T_p_upper(b) + f ∣[k] T_p_lower.
```
Combining with `heckeT_p_fun_eq_coset_sum` and the diamond identity
`slash_M_infty_eq_diamond_slash_T_p_lower`, one recovers the `χ = 1` bridge.
For general `χ`, the "explicit `T_p_lower`" term would need to be replaced
by `f ∣[k] M_∞` (the `M_∞` rep also lies in `D_p_Gamma0 N p hp.pos`; see
`M_infty_mem_D_p_Gamma0` below). The combined argument then yields the
general-χ bridge. -/

/-- `M_∞ ∈ D_p_Gamma0 N p hp.pos` as a member of the double coset set.

`M_∞ = mapGL ℚ σ_p_specific · T_p_lower` (via `M_infty_eq_sigma_mul_T_p_lower`),
and `σ_p_specific ∈ Γ₀(N)`, so `mapGL ℚ σ_p_specific ∈ (Gamma0_pair N).H`.
Combined with `T_p_lower ∈ D_p_Gamma0` and the fact that `toSet` is closed
under left-`H`-multiplication, `M_∞ ∈ D_p_Gamma0`. -/
lemma M_infty_mem_D_p_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    M_infty N p hp.pos hpN ∈ HeckeCoset.toSet (D_p_Gamma0 N p hp.pos) := by
  -- Step 1: M_∞ = σ_p · T_p_lower, with σ_p ∈ H.
  have h_factor : M_infty N p hp.pos hpN =
      (mapGL ℚ (sigma_p_specific N p hp.pos hpN)) *
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) :=
    M_infty_eq_sigma_mul_T_p_lower N p hp.pos hpN
  have h_sigma_H : (mapGL ℚ (sigma_p_specific N p hp.pos hpN) : GL (Fin 2) ℚ) ∈
      (Gamma0_pair N).H :=
    Subgroup.mem_map.mpr ⟨sigma_p_specific N p hp.pos hpN,
      sigma_p_specific_mem_Gamma0 N p hp.pos hpN, rfl⟩
  -- Step 2: T_p_lower ∈ D_p_Gamma0, so T_p_lower = h₁ · rep · h₂.
  have hTl := T_p_lower_mem_D_p_Gamma0 N p hp hpN
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hTl
  obtain ⟨h₁, hh₁, h₂, hh₂, hTl_eq⟩ := hTl
  -- Step 3: M_∞ = (σ_p · h₁) · rep · h₂, with σ_p · h₁ ∈ H.
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  refine ⟨(mapGL ℚ (sigma_p_specific N p hp.pos hpN)) * h₁,
    (Gamma0_pair N).H.mul_mem h_sigma_H hh₁, h₂, hh₂, ?_⟩
  rw [h_factor, hTl_eq]; group

/-- **Bridge at `χ = 1`**: `heckeT_p_fun f = heckeSlash_gen D_p_Gamma0 ⇑f`
for `f ∈ modFormCharSpace k 1`. This is a direct invocation of
`heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one`, stated in the
bridge hypothesis form. -/
theorem heckeSlash_gen_eq_heckeT_p_fun_charSpace_one (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos)
      (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
    heckeT_p_fun k p hp hpN (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  (heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one k p hp hpN f).symm

/-! ### Trivial-χ functional equivariance via the explicit path

For `χ = 1`, the `heckeSlash_gen` functional χ-equivariance is established
two ways:
1. Directly via `heckeSlash_gen_slash_invariant` (the `χ = 1` case treats
   the χ-factor as `1`). This is `heckeSlash_gen_functional_equivariance_D_p_Gamma0_trivial`.
2. Through the explicit-rep path: the χ=1 bridge combined with
   `heckeT_p_fun_slash_comm_charSpace` at `χ = 1`. -/

/-- **Functional χ-equivariance at `χ = 1`, via the explicit path**: this
reproduces `heckeSlash_gen_functional_equivariance_D_p_Gamma0_trivial` by
going through `heckeT_p_fun` instead of directly through
`heckeSlash_gen_slash_invariant`. Serves as a consistency checkpoint
between the abstract and explicit paths. -/
theorem heckeSlash_gen_functional_equivariance_D_p_Gamma0_trivial_via_explicit
    (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ))
    (g : ↥(Gamma0 N)) :
    (heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos) (⇑f : ℍ → ℂ)) ∣[k]
      mapGL ℝ (g : SL(2, ℤ)) =
    (↑((1 : (ZMod N)ˣ →* ℂˣ) (Gamma0MapUnits g)) : ℂ) •
      heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos) (⇑f : ℍ → ℂ) := by
  have h_bridge :
      heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos) (⇑f : ℍ → ℂ) =
      heckeT_p_fun k p hp hpN f :=
    heckeSlash_gen_eq_heckeT_p_fun_charSpace_one k p hp hpN ⟨f, hf⟩
  exact heckeSlash_gen_functional_equivariance_D_p_Gamma0_of_bridge
    k (1 : (ZMod N)ˣ →* ℂˣ) p hp hpN hf h_bridge g

/-! ### Summary

For `f ∈ modFormCharSpace k χ`, the functional χ-equivariance holds
**unconditionally at the explicit level** `heckeT_p_fun`:
```
heckeT_p_fun k p hp hpN f ∣[k] mapGL ℝ g = χ(Gamma0MapUnits g) • heckeT_p_fun k p hp hpN f
```
(See `heckeT_p_fun_functional_equivariance_D_p_Gamma0`.)

For the **abstract** `heckeSlash_gen (Gamma0_pair N) k (D_p_Gamma0 N p hp.pos)`,
the functional χ-equivariance reduces (via
`heckeSlash_gen_functional_equivariance_D_p_Gamma0_of_bridge`) to the bridge
```
heckeSlash_gen D_p_Gamma0 ⇑f = heckeT_p_fun f
```
which is established unconditionally at `χ = 1`
(`heckeSlash_gen_eq_heckeT_p_fun_charSpace_one`).

The key pragmatic consequence — that the Hecke operator preserves
`modFormCharSpace k χ` for `D_p_Gamma0` with `p ∤ N`, for **all** `χ` — is
established via `heckeT_p_preserves_modFormCharSpace` (Hecke_T_p.lean),
which works at the explicit `heckeT_p` level without requiring the abstract
heckeSlash bridge for general χ.

Thus the full general-χ Hecke algebra action on each character eigenspace
is available via the `heckeT_p_all_charRestrict` / `heckeT_n_charRestrict`
machinery (HeckeRingHomCharSpace.lean), bypassing the abstract
heckeSlash_gen sum altogether. -/

end HeckeRing.GL2
