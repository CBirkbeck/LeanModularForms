import Mathlib
open Complex Real Set

-- Derivative of chordSegment z₁ z₂ (t - c) is z₂ - z₁
noncomputable def chordSegment (z₁ z₂ : ℂ) : ℝ → ℂ := fun t => (1 - t) • z₁ + t • z₂

lemma hasDerivAt_chordSegment_shift (z₁ z₂ : ℂ) (c t : ℝ) :
    HasDerivAt (fun t' : ℝ => chordSegment z₁ z₂ (t' - c)) (z₂ - z₁) t := by
  unfold chordSegment
  have hfun : (fun t' : ℝ => (1 - (t' - c)) • z₁ + (t' - c) • z₂) = 
              (fun t' : ℝ => z₁ + (t' - c) • (z₂ - z₁)) := by
    ext t'
    simp only [sub_smul, one_smul, smul_sub]
    ring
  simp only [hfun]
  have h1 : HasDerivAt (fun t' : ℝ => (↑t' : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t' : ℝ => (↑t' : ℂ) - (↑c : ℂ)) (1 - 0) t := h1.sub (hasDerivAt_const t (↑c : ℂ))
  simp only [sub_zero] at h2
  have h3 : HasDerivAt (fun t' : ℝ => ((↑t' : ℂ) - (↑c : ℂ)) • (z₂ - z₁)) ((1 : ℂ) • (z₂ - z₁)) t := 
    h2.smul_const (z₂ - z₁)
  simp only [one_smul] at h3
  have h4 : HasDerivAt (fun t' : ℝ => z₁ + ((↑t' : ℂ) - (↑c : ℂ)) • (z₂ - z₁)) (0 + (z₂ - z₁)) t :=
    (hasDerivAt_const t z₁).add h3
  simp only [zero_add] at h4
  -- Show the functions are equal by explicit simplification
  have heq : (fun t' : ℝ => z₁ + (t' - c) • (z₂ - z₁)) = 
             (fun t' : ℝ => z₁ + ((↑t' : ℂ) - (↑c : ℂ)) • (z₂ - z₁)) := by
    ext t'
    congr 1
    -- Need to show: (t' - c) • (z₂ - z₁) = ((↑t' : ℂ) - (↑c : ℂ)) • (z₂ - z₁)
    rw [Complex.real_smul, Complex.ofReal_sub]
  rw [heq]
  exact h4
  
#check hasDerivAt_chordSegment_shift