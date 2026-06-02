# Sphere Packing Contour Integrals via Generalized Residue Theorem

## Goal

Apply the generalized residue theorem (HW Theorem 3.3) to compute the contour
integrals in Viazovska's E₈ sphere packing proof, replacing the rectangular
contour deformation approach with a direct CPV computation.

## The Integral

The magic function `a(r)` is defined via contour integrals of
`φ₀(-1/(z+1)) · (z+1)² · e^{πirz}` along paths from `-1` to `i`.

The original Viazovska contour is triangular (with an arc along the unit circle).
The Sphere-Packing-Lean formalization deforms this to rectangular segments
(`-1 → -1+i → i`) to avoid the cusp singularity at `z = -1`.

## Our Approach

Using `generalizedResidueTheorem_simplePoles` or `generalizedResidueTheorem`,
we can work directly with the original triangular contour, handling the
cusp at `z = -1` via Cauchy principal value.

## Status

Planning phase — studying the exact integral structure.
