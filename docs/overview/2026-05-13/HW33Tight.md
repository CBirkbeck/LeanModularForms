# /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33Tight.lean

## theorem `LeanModularForms.hw_3_3_tight`
- **Type**: For open `U`, finset `S ⊆ U`, `f` meromorphic on `U \ S`,
  closed null-homologous `PwC1Immersion` `γ` in `U`, conditions (A')+(B),
  CPV-vanishing of the higher-order polar part and holomorphic remainder,
  integrability assumptions, and CPV identification of the simple-pole
  part `hPV_sing`:
  `HasCauchyPVOn S f γ.toPiecewiseC1Path
    (2πI * ∑ s ∈ S, generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s)`.
- **What**: The "tight" paper-style form of Hungerbühler–Wasem Theorem 3.3.
  Compared to `generalizedResidueTheorem_higherOrder_under_B_closed`, the
  Laurent decomposition is **definitional** (extracted from condition (B)
  via `laurentHigherOrderPolar` and `laurentHolomorphicRemainder`), so the
  user no longer supplies `h_decomp`, `h_polar`, `h_holo`.
- **How**: One-shot reduction — calls
  `generalizedResidueTheorem_higherOrder_under_B_closed` with arguments
  `laurentHigherOrderPolar hCondB` and `laurentHolomorphicRemainder hCondB`
  and the decomposition identity `f_minus_pp_eq_higherOrder_plus_holo hCondB`
  (which holds definitionally from condition (B)'s Laurent-compatibility
  data), passing through the remaining cancellation/integrability
  hypotheses as-is.
- **Hypotheses**:
  - `IsOpen U`, `↑S ⊆ U`, `DifferentiableOn ℂ f (U \ ↑S)`;
  - `IsNullHomologous γ U`;
  - per-pole `MeromorphicAt f s`;
  - condition (A') and condition (B) (`SatisfiesConditionA'`,
    `SatisfiesConditionB`);
  - `h_polar_cancel` and `h_holo_cancel` (CPV vanishing of the higher-order
    polar part and of the holomorphic remainder, both on `γ`);
  - `hI_polar`, `hI_holo`, `hI_sing` (interval integrability of the
    respective CPV integrands at every cutoff `ε`);
  - `hPV_sing` for the simple-pole part (typically from `B-6` closure).
- **Uses-from-project**:
  - `LeanModularForms.ForMathlib.HW33LaurentPolarPart`
    (`laurentHigherOrderPolar`, `laurentHolomorphicRemainder`,
    `f_minus_pp_eq_higherOrder_plus_holo`).
  - `LeanModularForms.ForMathlib.HW33Closed`
    (`generalizedResidueTheorem_higherOrder_under_B_closed`).
  - `LeanModularForms.ForMathlib.ResidueLinearity` (residue / `principalPartSum`,
    transitively used in `hPV_sing` typing).
  - `PwC1Immersion`, `IsNullHomologous`, `SatisfiesConditionA'`,
    `SatisfiesConditionB`, `cpvIntegrandOn`, `HasCauchyPVOn`,
    `principalPartSum`, `residue`, `poleOrderAt`,
    `generalizedWindingNumber` (all transitively imported).
- **Used by**: The "TIGHT-5" milestone of the mathlib-PR ticket lane;
  serves as the public paper-style API for HW Theorem 3.3 in the avoidance
  formulation.
- **Visibility**: public `theorem`; namespace `LeanModularForms`,
  inside `noncomputable section`.
- **Lines**: 63-84.
- **Notes**: The proof body is a single application of
  `generalizedResidueTheorem_higherOrder_under_B_closed` — no tactics.
  Header docstring explains that compared to the original
  `generalizedResidueTheorem`, this eliminates 4 function arguments and
  the decomposition equation hypothesis (since the polar/holomorphic
  parts are now definitional from condition (B)).

## File Summary
A single public theorem `LeanModularForms.hw_3_3_tight` (paper-style
form of HW 3.3). The file is a thin façade: it composes the Laurent
polar-part extraction (`HW33LaurentPolarPart`) with the closed-form
generalised residue theorem (`HW33Closed`) by instantiating
`laurentHigherOrderPolar` and `laurentHolomorphicRemainder` automatically
from `SatisfiesConditionB` data, eliminating three hypotheses
(`h_decomp`, `h_polar`, `h_holo`). The user still supplies CPV-vanishing
of polar/holomorphic remainders, integrability, and the simple-pole CPV
identification `hPV_sing`. No `sorry`. Per the `tickets-tight.md` log,
this file corresponds to "TIGHT-5".
