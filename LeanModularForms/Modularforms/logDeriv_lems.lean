import LeanModularForms.Modularforms.tendstolems
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Separation.CompletelyRegular


open  TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical


theorem logDeriv_tprod_eq_tsum2 {s : Set ℂ} (hs : IsOpen s) (x : s) (f : ℕ → ℂ → ℂ)
    (hf : ∀ i, f i x ≠ 0)
    (hd : ∀ i : ℕ, DifferentiableOn ℂ (f i) s) (hm : Summable fun i ↦ logDeriv (f i) ↑x)
    (htend : MultipliableLocallyUniformlyOn f s) (hnez : ∏' (i : ℕ), f i ↑x ≠ 0) :
    logDeriv (∏' i : ℕ, f i ·) x = ∑' i : ℕ, logDeriv (f i) x := by
    have h2 := Summable.hasSum hm
    rw [Summable.hasSum_iff_tendsto_nat hm] at h2
    apply symm
    rw [← Summable.hasSum_iff hm]
    rw [Summable.hasSum_iff_tendsto_nat hm]
    let g := (∏' i : ℕ, f i ·)
    have := logDeriv_tendsto (f := fun (n : ℕ) ↦ ∏ i ∈ Finset.range n, (f i)) (g := g) (s := s) hs
      (p := atTop)
    simp only [eventually_atTop, ge_iff_le, ne_eq, forall_exists_index, Subtype.forall, g] at this
    have HT := this x x.2 ?_ ?_ ?_ ?_
    conv =>
      enter [1]
      ext n
      rw [← logDeriv_prod _ _ _ (by intro i hi; apply hf i)
        (by intro i hi; apply (hd i x x.2).differentiableAt; exact IsOpen.mem_nhds hs x.2)]
    apply HT.congr
    intro m
    congr
    ext i
    simp only [Finset.prod_apply]
    have:= htend.hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
    convert this
    simp
    use 0
    intro b hb
    rw [DifferentiableOn]
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hp : ∀ (i : ℕ), i ∈ Finset.range b →  DifferentiableAt ℂ (f i) z := by
      intro i hi
      have := (hd i z hz).differentiableAt
      apply this
      exact IsOpen.mem_nhds hs hz
    have := DifferentiableAt.finset_prod hp
    convert this
    · exact hnez


theorem logDeriv_tprod_eq_tsum  {s : Set ℂ} (hs : IsOpen s) (x : s) (f : ℕ → ℂ → ℂ)
    (hf : ∀ i, f i x ≠ 0)
    (hd : ∀ i : ℕ, DifferentiableOn ℂ (f i) s) (hm : Summable fun i ↦ logDeriv (f i) ↑x)
    (htend : TendstoLocallyUniformlyOn (fun n ↦ ∏ i ∈ Finset.range n, f i)
    (fun x ↦ ∏' (i : ℕ), f i x) atTop s) (hnez : ∏' (i : ℕ), f i ↑x ≠ 0) :
    logDeriv (∏' i : ℕ, f i ·) x = ∑' i : ℕ, logDeriv (f i) x := by
    have h2 := Summable.hasSum hm
    rw [Summable.hasSum_iff_tendsto_nat hm] at h2
    apply symm
    rw [← Summable.hasSum_iff hm]
    rw [Summable.hasSum_iff_tendsto_nat hm]
    let g := (∏' i : ℕ, f i ·)
    have := logDeriv_tendsto (f := fun n ↦ ∏ i ∈ Finset.range n, (f i)) (g:=g) (s := s) hs (p := atTop)
    simp only [eventually_atTop, ge_iff_le, ne_eq, forall_exists_index, Subtype.forall, g] at this
    have HT := this x x.2 ?_ ?_ ?_ ?_
    conv =>
      enter [1]
      ext n
      rw [← logDeriv_prod _ _ _ (by intro i hi; apply hf i)
        (by intro i hi; apply (hd i x x.2).differentiableAt; exact IsOpen.mem_nhds hs x.2)]
    apply HT.congr
    intro m
    congr
    ext i
    simp only [Finset.prod_apply]
    exact htend
    use 0
    intro b hb
    rw [DifferentiableOn]
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hp : ∀ (i : ℕ), i ∈ Finset.range b →  DifferentiableAt ℂ (f i) z := by
      intro i hi
      have := (hd i z hz).differentiableAt
      apply this
      exact IsOpen.mem_nhds hs hz
    have := DifferentiableAt.finset_prod hp
    convert this
    · exact hnez


lemma logDeriv_one_sub_exp (r : ℂ) : logDeriv (fun z => 1 - r * cexp (z)) =
    fun z => -r * cexp z / (1 - r * cexp ( z)) := by
  ext z
  rw [logDeriv]
  simp only [Pi.div_apply, differentiableAt_const, differentiableAt_exp, DifferentiableAt.fun_mul,
    deriv_fun_sub, deriv_const', deriv_fun_mul, zero_mul, Complex.deriv_exp, zero_add, zero_sub,
    neg_mul]

lemma logDeriv_one_sub_exp_comp (r : ℂ) (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    logDeriv ((fun z => 1 - r * cexp (z)) ∘ g) =
    fun z => -r * ((deriv g) z) * cexp (g z) / (1 - r * cexp (g (z))) := by
  ext y
  rw  [logDeriv_comp, logDeriv_one_sub_exp]
  simp only [neg_mul]
  ring
  simp only [differentiableAt_const, differentiableAt_exp, DifferentiableAt.fun_mul,
    DifferentiableAt.fun_sub]
  exact hg y

lemma logDeriv_q_expo_summable (r : ℂ) (hr : ‖r‖ < 1) : Summable fun n : ℕ =>
    (n * r^n / (1 - r^n)) := by
  have := aux47 r hr
  have h1 : Tendsto (fun n : ℕ => (1 : ℂ)) atTop (𝓝 1) := by simp
  have h2 := Filter.Tendsto.div h1 this (by simp)
  rw [Metric.tendsto_atTop] at h2
  simp only [gt_iff_lt, ge_iff_le, Pi.div_apply, one_div, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, dist_eq_norm] at h2
  have h3 := h2 1 (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat (g := fun n => 2 * ‖n * r^n‖)
  apply Summable.mul_left
  simp
  · have := (summable_norm_pow_mul_geometric_of_norm_lt_one 1 hr)
    simp at this
    apply this
  · simp
    obtain ⟨N, hN⟩ := h3
    use N
    intro n hn
    have h4 := hN n hn
    have := norm_lt_of_mem_ball h4 (E := ℂ)
    simp at *
    rw [div_eq_mul_inv]
    rw [mul_comm]
    gcongr
    apply le_trans this.le
    norm_cast

lemma func_div (a b c d : ℂ → ℂ) (x : ℂ) (hb : b x ≠ 0) (hd :  d x ≠ 0) :
     (a / b) x = (c /d) x ↔ (a * d) x = (b * c) x := by
  constructor
  intro h
  simp at *
  rw [div_eq_div_iff] at h
  nth_rw 2 [mul_comm]
  exact h
  exact hb
  exact hd
  intro h
  simp only [Pi.div_apply]
  rw [div_eq_div_iff]
  simp only [Pi.mul_apply] at h
  nth_rw 2 [mul_comm]
  exact h
  apply hb
  apply hd


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma Set.EqOn.deriv {f g : 𝕜 → F} {s : Set 𝕜} (hfg : s.EqOn f g) (hs : IsOpen s) :
    s.EqOn (deriv f) (deriv g) := by
  intro x hx
  rw [← derivWithin_of_isOpen hs hx, ← derivWithin_of_isOpen hs hx]
  exact derivWithin_congr hfg (hfg hx)

lemma deriv_EqOn_congr {f g : ℂ → ℂ} (s : Set ℂ) (hfg : s.EqOn f g) (hs : IsOpen s) :
    s.EqOn (deriv f) ( deriv g) := by
  intro x hx
  rw [← derivWithin_of_isOpen hs hx]
  rw [← derivWithin_of_isOpen hs hx]
  apply derivWithin_congr hfg
  apply hfg hx



lemma logDeriv_eqOn_iff {E 𝕜 : Type*} [NontriviallyNormedField E] [NontriviallyNormedField 𝕜]
    [IsRCLikeNormedField 𝕜] [NormedAlgebra 𝕜 E] {f g : 𝕜 → E} {s : Set 𝕜}
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hs2 : IsOpen s) (hsc : IsPreconnected s) (hgn : ∀ x ∈ s, g x ≠ 0) (hfn : ∀ x ∈ s, f x ≠ 0) :
    EqOn (logDeriv f) (logDeriv g) s ↔ ∃ (z : E), z ≠ 0 ∧ s.EqOn f (z • g) := by
  by_cases hs : s.Nonempty
  · constructor
    · simp_rw [logDeriv]
      intro h
      obtain ⟨t, ht⟩ := hs
      refine ⟨(f t) * (g t)⁻¹, mul_ne_zero (hfn t ht) (by simpa using (hgn t ht)), fun y hy => ?_⟩
      · have hderiv : s.EqOn (deriv (f * g⁻¹)) (deriv f * g⁻¹ - f * deriv g / g ^ 2) := by
          intro z hz
          rw [deriv_mul (hf.differentiableAt (hs2.mem_nhds hz)) ((hg.differentiableAt
            (hs2.mem_nhds hz)).inv (hgn z hz))]
          simp only [Pi.inv_apply, show g⁻¹ = (fun x => x⁻¹) ∘ g by rfl, deriv_inv, neg_mul,
            deriv_comp z (differentiableAt_inv (hgn z hz)) (hg.differentiableAt (hs2.mem_nhds hz)),
            mul_neg, Pi.sub_apply, Pi.mul_apply, comp_apply, Pi.div_apply, Pi.pow_apply]
          ring
        have hfg : EqOn (deriv (f * g⁻¹)) 0 s := by
          apply hderiv.trans
          intro z hz
          simp only [Pi.sub_apply, Pi.mul_apply, Pi.inv_apply, Pi.div_apply, Pi.pow_apply,
            Pi.zero_apply]
          suffices deriv f z * g z - f z * deriv g z = 0 by
            field_simp [hgn z hz]
            simp [this]
          have H := h hz
          simp_rw [Pi.div_apply, div_eq_div_iff (hfn z hz) (hgn z hz), mul_comm] at H
          simp [← H, mul_comm]
        letI := IsRCLikeNormedField.rclike 𝕜
        obtain ⟨a, ha⟩ := IsOpen.exists_is_const_of_deriv_eq_zero (f := f * g⁻¹) (s := s) hs2 hsc
          (hf.mul (DifferentiableOn.inv hg hgn)) hfg
        have hay := ha y hy
        have hat := ha t ht
        simp only [ne_eq, Pi.mul_apply, Pi.inv_apply, Pi.smul_apply, smul_eq_mul] at *
        rw [hat, ← hay]
        field_simp [hgn y hy]
    · rintro ⟨z, hz0, hz⟩ x hx
      simp [logDeriv_apply, hz.deriv hs2 hx, hz hx, deriv_const_smul _
        (hg.differentiableAt (hs2.mem_nhds hx)), mul_div_mul_left (deriv g x) (g x) hz0]
  ·  simpa [not_nonempty_iff_eq_empty.mp hs] using ⟨1, one_ne_zero⟩

lemma logDeriv_eqOn_iff2 (f g : ℂ → ℂ) (s : Set ℂ) (hf : DifferentiableOn ℂ f s)
    (hg : DifferentiableOn ℂ g s) (hs : s.Nonempty) (hs2 : IsOpen s) (hsc : Convex ℝ s)
    (hgn : ∀ x, x ∈ s →  g x ≠ 0) (hfn : ∀ x, x ∈ s → f x ≠ 0) : EqOn (logDeriv f) (logDeriv g) s ↔
    ∃( z : ℂ),  z ≠ 0 ∧  EqOn (f) (z • g) s := by
  apply logDeriv_eqOn_iff hf hg hs2 (hsc.isPreconnected) hgn hfn
