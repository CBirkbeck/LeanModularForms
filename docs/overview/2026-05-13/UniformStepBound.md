# UniformStepBound.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/PVInfrastructure/UniformStepBound.lean`

## Imports
- `LeanModularForms.ForMathlib.GeneralizedResidueTheory.PVInfrastructure.AnnulusBounds`
- `LeanModularForms.ForMathlib.GeneralizedResidueTheory.PVInfrastructure.SingularAnnulus`

## Declarations

### `lemma pv_step_bound_ratio_two_uniform`
- **Type**: `{γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ} (hab : a < b) (hat₀ : t₀ ∈ Set.Ioo a b) (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L) (hL : L ≠ 0) (hγ_meas : Measurable γ) (hγ_cont_deriv : ContinuousOn (deriv γ) (Set.Icc a b)) (hγ_cont : ContinuousOn γ (Set.Icc a b)) (h_inj : ∀ t ∈ Set.Icc a b, γ t = γ t₀ → t = t₀) : ∃ Kstep > 0, ∃ δ > 0, ∀ ε₁ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ ε₁ → ε₁ ≤ 2 * ε₂ → ε₁ < δ → let I := fun ε => ∫ t in a..b, if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0; ‖I ε₂ - I ε₁‖ ≤ Kstep * ε₁`
- **What**: Uniform (ε-independent) step bound for the dyadic principal-value approximations. For a C² curve γ with γ′(t₀)=L≠0 and γ injective at t₀, the difference `I(ε₂) - I(ε₁)` of cutoff integrals (with cutoff `‖γ(t)-γ(t₀)‖ > ε`) is bounded by `Kstep · ε₁` whenever `ε₂ ≤ ε₁ ≤ 2ε₂` and `ε₁ < δ`, with a constant `Kstep` independent of ε.
- **How**: Combines (a) remainder analysis `remainder_bounded_of_C2` to get `f(t) - (t-t₀)⁻¹` bounded by `C`, (b) singular annulus bound `singular_annulus_bound_explicit` for the pure pole part `(↑(t-t₀))⁻¹` over an annulus, (c) gamma lower/upper bounds `gamma_lower_bound_of_hasDerivAt`/`gamma_upper_bound_of_hasDerivAt` to control `‖γ(t)-γ(t₀)‖` via `|t-t₀|`, and (d) `no_return_of_inj_continuous` for a far-away separation `ρ`. Decomposes `I(ε₂) - I(ε₁)` as an annulus integral via `cutoff_diff_eq_annulus_integral`, splits the integrand into singular `(t-t₀)⁻¹` + remainder `r`, applies the singular bound from `h_singular` and the remainder bound from `remainder_integral_bound_on_annulus`, and uses `norm_add_le` to combine them. Sets `Kstep = 4 max(0,C)/‖L‖ + Csing`.
- **Hypotheses**: `a < b`; `t₀ ∈ (a, b)`; `γ ∈ C²` at `t₀`; `deriv γ t₀ = L ≠ 0`; `γ` measurable; `deriv γ` continuous on `[a,b]`; `γ` continuous on `[a,b]`; `γ` injective on `[a,b]` at the value `γ t₀`.
- **Uses from project**: `remainder_bounded_of_C2`, `singular_annulus_bound_explicit`, `gamma_lower_bound_of_hasDerivAt`, `gamma_upper_bound_of_hasDerivAt`, `no_return_of_inj_continuous`, `cutoff_integrand_intervalIntegrable`, `cutoff_diff_eq_annulus_integral`, `remainder_integral_bound_on_annulus`.
- **Used by**: unused in file.
- **Visibility**: public (lemma).
- **Lines**: 27–201.
- **Notes**: Long proof (>30 lines, ~175 tactic lines). Uses `noncomputable section`. Uses `let` bindings for `δ₁`, `δ`, `Kstep`, `f`, `r`, `I`. No `sorry`, no `axiom`, no `set_option`, no `native_decide`. Uses `push Not` (note unusual capitalisation appearing in the source).

## File Summary

UniformStepBound.lean contains a single major lemma `pv_step_bound_ratio_two_uniform` (one lemma, no other declarations) that delivers the central uniform step-bound estimate in the principal-value (PV) infrastructure layer. The lemma fuses four prerequisite estimates — remainder boundedness for C² curves, an explicit singular annulus bound, two-sided velocity estimates from `HasDerivAt`, and a separation bound from continuity+injectivity — into one ε-independent constant `Kstep = 4·max(0,C)/‖L‖ + Csing`. The proof factors the cutoff difference as `(t-t₀)⁻¹`-pole part plus a bounded remainder, then bounds each piece separately on the annulus `ε₂ < ‖γ(t)-γ(t₀)‖ ≤ ε₁`. The lemma is presented as the file's "Main Result"; downstream uses are in other files (none within this file). Build-relevant notes: `noncomputable section` is opened at line 25 and closed at line 202; the imports point to two sibling PVInfrastructure modules.
