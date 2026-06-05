/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.HeckeRIngs.GL2.Unified.Gamma0RingDn

/-!
# The Shimura-convention companion Hecke action `Ψ_χ` — design notes and obstruction

This file was intended to construct the **direct** (non-adjugate) χ-twisted action of the
Hecke ring `𝕋 (Gamma0_pair N) ℤ` on `modFormCharSpace k χ` — the companion homomorphism
`Ψ_χ` that, unlike the existing `heckeRingHomCharSpace` (`Φ_χ`), would send the prime double
coset `D_p` to the `U_p` operator at the bad primes `p ∣ N`.

## The literal "slash by `deltaRep_gen`" construction is non-invariant (verified obstruction)

The existing `Φ_χ` (`twistedHeckeSlash_gen`) slashes a coset `D` by the **adjugates**
`tRep_gen D i = GL_adjugate (deltaRep_gen D i)` of the representatives.  The proposed direct
`Ψ_χ` slashes by `deltaRep_gen D i = σᵢ · rep(D)` themselves.  This is provably **not**
twisted-invariant, and therefore does not land in `modFormCharSpace k χ`.  The precise
reason:

* `decompQuot (Gamma0_pair N) g = H ⧸ ((g H g⁻¹) ∩ H)` indexes the decomposition
  `HgH = ⊔ᵢ δᵢ · H` into **right cosets** `δᵢ · H` with `δᵢ = i.out · g` (see
  `decompQuot_coset_diff` and `DoubleCoset.doubleCoset_eq_iUnion_leftCosets`).
* For the un-adjugated representatives the `H`-correction lands on the **right**:
  `gamma0TripleDelta D h₁ h₂ = deltaRep_gen D ⟦h₁⟧ · κ` with `κ ∈ Γ₀(N)` (the existing
  `gamma0TripleDelta_eq_deltaRep_mul_correction`).  Hence
  `f ∣ (h₁ · rep · h₂) = (f ∣ δ_q) ∣ κ`.
* A right `Γ₀(N)`-correction on a **slashed** term `f ∣ δ_q` does *not* simplify: it would
  require `(f ∣ δ_q) ∣ κ = χ(Δ_up κ)⁻¹ • (f ∣ δ_q)` for every `κ ∈ Γ₀(N)`, i.e. that
  `f ∣ δ_q` is a `χ`-eigenform for the *full* `Γ₀(N)`.  Since `δ_q` has determinant `p` and
  conjugates `Γ₀(N)` out of itself, this is false.
* By contrast the **adjugate** `Φ_χ` works precisely because `GL_adjugate` turns the right
  correction into a *left* one (`adj(h₁·rep·h₂) = adj(κ)·tRep_gen(q)`), which is absorbed by
  `f ∣ adj(κ)` via `f`'s twisted-invariance.  See `twisted_weighted_slash_tRep_gen_of_mem`.

Since slashing by `σ_Q ∈ Γ₀(N)` keeps each `δᵢ · σ_Q` inside the *same* right coset
`δᵢ · H` (no permutation of the summands), **no choice of weight** can repair invariance of
`∑ᵢ w(i) • (f ∣ δᵢ)`: per-term invariance under all of `Γ₀(N)` would be required, which is
impossible.  The same argument with `γ ∈ Γ₁(N)` shows the sum is not even a modular form (the
output is not `Γ₁(N)`-invariant).  The obstruction is recorded as the lemma
`direct_correction_on_right` below (the right `Γ₀(N)`-factor that cannot be absorbed).

**The bad-prime claim is false for these representatives.**  At `p ∣ N` the right-coset
representatives are `δᵣ = jₒ · diag(1,p) = [[1,0],[N·r,p]]` for `r = 0,…,p−1` (each has
upper-left unit `1`, hence χ-weight `1`); see `lunip_inject` /
`decompQuot_Npow_natcard`.  These are the *lower*-unipotent translates of `diag(1,p)`, **not**
the upper-triangular `U_p` representatives `T_p_upper(b) = [[1,b],[0,p]]` — indeed
`δᵣ · T_p_upper(b)⁻¹ = [[1,−b/p],[N·r,…]] ∉ Γ₁(N)` unless `p ∣ b`, so the two sums are not
equal even for `Γ₁(N)`-forms.  The genuine `U_p` reps `T_p_upper(b)` are the **left**-coset
representatives `Γ₀(N) \ Γ₀(N)·diag(1,p)·Γ₀(N)`, confirming the left-coset reformulation below
is the correct one.

## The mathematically correct companion: the left-coset decomposition

A Hecke operator must sum over the **left cosets** `H \ HgH = ⊔ⱼ H · βⱼ`, where right
multiplication by `γ ∈ H` *permutes* the left cosets (`H·βⱼ·γ = H·β_{π(j)}`), and the
correction `βⱼ·γ = h · β_{π(j)}` lands on the **left**, hitting `f` (and being absorbed by
twisted-invariance).  For `D_p = Γ₀(N)·diag(1,p)·Γ₀(N)` the left-coset representatives are
exactly `T_p_upper(b) = [[1,b],[0,p]]` (`b = 0,…,p−1`) and `T_p_lower = [[p,0],[0,1]]` — the
representatives appearing in `heckeT_p_all`; at a bad prime `p ∣ N` only the `p`
upper-triangular ones survive, giving `U_p` with weight `1` on each (every upper-left entry
is `1`), i.e. exactly the desired `Ψ_χ(D_p) = U_p|_χ`.

The left-coset representatives are `βⱼ = rep(D) · jₒ` with `jₒ ∈ Γ₀(N)` ranging over the
quotient `H ⧸ ((g⁻¹ H g) ∩ H)` (note: `g⁻¹ H g = adj(g) H adj(g)⁻¹`, so this is the right-
coset quotient `decompQuot` of `adj(rep(D))` — but `adj(rep(D)) ∉ Δ₀(N)` at bad primes, so
this quotient must be formed from the bare subgroup `(g⁻¹ H g) ∩ H ≤ H`, which is *not* the
existing `decompQuot (Gamma0_pair N) (rep D)`).

Building `Ψ_χ` therefore requires a **new** finite left-coset-decomposition quotient
(mirroring `decompQuot`'s finiteness via the symmetry of the commensurator) together with a
full re-derivation of the per-coset slash, its `Γ₀(N)`-invariance, and — the substantial
part — its multiplicativity (the fiber-sum combinatorics of `twistedHeckeSlash_gen_comp`,
`twistedHeckeSumFunction_mul` re-expressed for the *opposite*-order per-coset product, an
anti-law turned into a hom by `Gamma0_pair_HeckeAlgebra_mul_comm`).  This is a major
standalone development rather than a sign-flipped mirror of `TwistedHeckeRing.lean`, and is
left for future work; the diagnosis above records exactly why the naive construction fails
and what the correct construction is.

## What this file currently provides

The non-adjugate per-coset slash `directHeckeSlash_gen` is defined together with its additive
and `ℂ`-linear behaviour (these hold for the *function-level* operator regardless of
invariance).  It is **not** promoted to an endomorphism of `modFormCharSpace k χ`, because —
as proved above — its output is not twisted-invariant.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn
open HeckeRing
open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]
variable {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- Positivity of the rational determinant of a (non-adjugated) `Γ₀(N)` Hecke
representative `deltaRep_gen D i = σᵢ · rep(D)`. -/
lemma deltaRep_gen_det_pos (D : HeckeCoset (Gamma0_pair N))
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    0 < (deltaRep_gen (N := N) D i : GL (Fin 2) ℚ).det.val := by
  simpa [deltaRep_gen] using (deltaRep_gen (N := N) D i).prop.2.1

private lemma smul_slash_deltaRep_gen (k : ℤ) (D : HeckeCoset (Gamma0_pair N))
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) (c : ℂ) (f : ℍ → ℂ) :
    (c • f) ∣[k] (deltaRep_gen (N := N) D i : GL (Fin 2) ℚ) =
      c • (f ∣[k] (deltaRep_gen (N := N) D i : GL (Fin 2) ℚ)) :=
  smul_slash_pos_det k c f _ (deltaRep_gen_det_pos (N := N) D i)

/-- The **direct** (non-adjugate) χ-twisted Hecke slash attached to a `Γ₀(N)` Hecke coset:
slashing by the right-coset representatives `deltaRep_gen D i = σᵢ · rep(D)` themselves,
weighted by the χ-character of their upper-left unit.

⚠ This is *not* `Γ₀(N)`-twisted-invariant in general (see the module docstring) — it is the
naive companion to `twistedHeckeSlash_gen` and is recorded here only at the function level.
The genuine `U_p`-hitting companion `Ψ_χ` requires the left-coset reformulation. -/
noncomputable def directHeckeSlash_gen (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
    (↑(delta0NebentypusWeight (N := N) χ D i) : ℂ) •
      (f ∣[k] (deltaRep_gen (N := N) D i : GL (Fin 2) ℚ))

@[simp] lemma directHeckeSlash_gen_add (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (f g : ℍ → ℂ) :
    directHeckeSlash_gen (N := N) k χ D (f + g) =
      directHeckeSlash_gen (N := N) k χ D f +
        directHeckeSlash_gen (N := N) k χ D g := by
  ext z
  simp [directHeckeSlash_gen, Finset.sum_add_distrib]

@[simp] lemma directHeckeSlash_gen_smul (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (c : ℂ) (f : ℍ → ℂ) :
    directHeckeSlash_gen (N := N) k χ D (c • f) =
      c • directHeckeSlash_gen (N := N) k χ D f := by
  simp only [directHeckeSlash_gen, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ext z
  rw [smul_slash_deltaRep_gen (N := N) k D i c f]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The obstruction, stated as a lemma.** For the direct (non-adjugate) representatives the
`Γ₀(N)`-correction in the right-coset decomposition lands on the *right* of the slashed
representative.  Concretely, for `h₁, h₂ ∈ Γ₀(N)`, with `q = ⟦h₁⟧` the corresponding class,
the representative `h₁ · rep(D) · h₂` factors as `deltaRep_gen D q · κ` with `κ ∈ Γ₀(N)`, so

`f ∣ (h₁ · rep(D) · h₂) = (f ∣ deltaRep_gen D q) ∣ κ`.

Twisted-invariance of `f` (a `χ`-eigenform under the *adjugate* action of `Γ₀(N)`) cannot
absorb this right factor, because `f ∣ deltaRep_gen D q` is not a `χ`-eigenform under
`Γ₀(N)`.  This is the formal record of why `directHeckeSlash_gen` is not invariant; it does
*not* assert invariance. -/
lemma direct_correction_on_right (D : HeckeCoset (Gamma0_pair N))
    (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (Gamma0_pair N).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H) (f : ℍ → ℂ) :
    f ∣[k] (h₁ * (HeckeCoset.rep D : GL (Fin 2) ℚ) * h₂) =
      (f ∣[k] (deltaRep_gen (N := N) D ⟦⟨h₁, hh₁⟩⟧ : GL (Fin 2) ℚ)) ∣[k]
        glMap (gamma0Correction (N := N) D ⟦⟨h₁, hh₁⟩⟧ h₁ h₂) := by
  set q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧ with hq
  have hκ : gamma0Correction (N := N) D q h₁ h₂ ∈ (Gamma0_pair N).H :=
    gamma0Correction_mem_H (N := N) D q h₁ hh₁ h₂ hh₂ (Quotient.out_eq q)
  have hδ : (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) =
      (deltaRep_gen (N := N) D q : GL (Fin 2) ℚ) * gamma0Correction (N := N) D q h₁ h₂ :=
    congrArg (fun x : (Gamma0_pair N).Δ ↦ (x : GL (Fin 2) ℚ))
      (gamma0TripleDelta_eq_deltaRep_mul_correction (N := N) D q h₁ hh₁ h₂ hh₂ hκ)
  rw [hδ]
  change f ∣[k] glMap _ = _
  rw [map_mul, SlashAction.slash_mul]
  rfl

end HeckeRing.GL2.Unified
