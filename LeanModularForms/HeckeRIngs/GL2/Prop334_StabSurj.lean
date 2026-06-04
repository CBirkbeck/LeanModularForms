/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Prop334
import Mathlib.Data.ZMod.Units

/-!
# Prop 3.34 — Stabilizer surjectivity on diamond characters

For `g ∈ Δ₀(N)` with `gcd(det g, N) = 1`, the stabilizer subgroup
`(ConjAct g • (Gamma0_pair N).H).subgroupOf (Gamma0_pair N).H` maps surjectively onto
`(ZMod N)ˣ` under `Gamma0MapUnits`. This is a key step for the preservation of
`modFormCharSpace k χ` under `heckeSlash_gen` (Prop 3.34-E).

## Main results

* `Gamma0MapUnits_surjOn_stab_diag` — surjectivity for the diagonal case `g = diag(1, k)`,
  the case used by `heckeT_p` for `p` coprime to `N`.
* `Gamma0MapUnits_surjOn_stab_transport` — transports stabilizer surjectivity across the
  `Γ₀(N)`-double coset action, using abelianness of `(ZMod N)ˣ`.
* `Gamma0MapUnits_surjOn_stab_of_diagReduction` — general form, given a factorization
  `g = γ_L · diag(1, k) · γ_R` with `γ_L, γ_R ∈ H`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
-/

namespace HeckeRing.GL2.Prop334

open Matrix CongruenceSubgroup HeckeRing.GLn Matrix.SpecialLinearGroup HeckeRing.GL2

open scoped Pointwise MatrixGroups

end HeckeRing.GL2.Prop334
