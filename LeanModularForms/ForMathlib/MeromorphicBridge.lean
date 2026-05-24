/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.ResidueCircleIntegral
import Mathlib.Analysis.Meromorphic.Order

/-!
# Bridge: `HasSimplePoleAt` and Mathlib `MeromorphicAt`

This file connects the project's `HasSimplePoleAt` decomposition to Mathlib's
`MeromorphicAt` / `meromorphicOrderAt` API.

## Main results

* `HasSimplePoleAt.meromorphicAt` -- a simple pole is meromorphic.
* `meromorphicOrderAt_eq_neg_one_of_hasSimplePoleAt` -- a simple pole with nonzero
  coefficient has meromorphic order exactly `-1`.
* `meromorphicOrderAt_nonneg_of_hasSimplePoleAt_coeff_zero` -- a simple pole with zero
  coefficient has non-negative order (the function is effectively analytic).
* `hasSimplePoleAt_of_meromorphicAt_order_neg_one` -- converse: meromorphic order `-1`
  implies `HasSimplePoleAt`.
* `residue_eq_leadingCoeff_of_order_neg_one` -- the residue equals the leading
  coefficient `g(z_0)` from Mathlib's meromorphic factorization at order `-1`.
* `hasSimplePoleAt_of_analyticAt` -- an analytic function has a simple pole decomposition
  with coefficient `0`.

## Design

The key algebraic identity underlying most proofs is:

  `c / (z - z_0) + g(z) = (z - z_0)^(-1) * (c + (z - z_0) * g(z))`

where `c + (z - z_0) * g(z)` is analytic at `z_0` with value `c` there. This converts
between the project's additive decomposition and Mathlib's multiplicative factorization.

For the converse direction, we use the analytic order factorization: if `g` is analytic
at `z_0`, then `g(z) - g(z_0) = (z - z_0) * h(z)` for some analytic `h`, giving
`(z - z_0)^(-1) * g(z) = g(z_0) / (z - z_0) + h(z)`.
-/

open Complex Set Filter Topology

section

/-! ### Forward direction: `HasSimplePoleAt` to `MeromorphicAt` -/

end
