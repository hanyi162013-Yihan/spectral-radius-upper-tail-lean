import SpectralRadiusUpperTail.CenteredConcentrationTransfer

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma centered_difference_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (c δ : ℝ) :
    μ.real {x | δ < |(c+f x-g x)-(∫ y, c+f y-g y ∂μ)|} ≤
      μ.real {x | δ/2 < |f x-(∫ y, f y ∂μ)|}+
      μ.real {x | δ/2 < |g x-(∫ y, g y ∂μ)|} := by
  have he : (∫ y, c+f y-g y ∂μ) = c+(∫ y, f y ∂μ)-(∫ y, g y ∂μ) := by
    have hcf : Integrable (fun y => c+f y) μ := (integrable_const c).add hf
    rw [integral_sub hcf hg, integral_add (integrable_const c) hf]
    simp
  rw [he]
  apply (measureReal_mono (s₂ :=
    {x | δ/2 < |f x-(∫ y, f y ∂μ)|} ∪
      {x | δ/2 < |g x-(∫ y, g y ∂μ)|}) ?_ (measure_ne_top _ _)).trans
    (measureReal_union_le _ _)
  intro x hx
  by_contra hh
  have hfδ : |f x-(∫ y, f y ∂μ)| ≤ δ/2 := by
    by_contra hn
    exact hh (Or.inl (lt_of_not_ge hn))
  have hgδ : |g x-(∫ y, g y ∂μ)| ≤ δ/2 := by
    by_contra hn
    exact hh (Or.inr (lt_of_not_ge hn))
  have ht := abs_sub (f x-(∫ y, f y ∂μ)) (g x-(∫ y, g y ∂μ))
  have he' : c+f x-g x-(c+(∫ y, f y ∂μ)-(∫ y, g y ∂μ)) =
      (f x-(∫ y, f y ∂μ))-(g x-(∫ y, g y ∂μ)) := by ring
  change δ < |c+f x-g x-(c+(∫ y, f y ∂μ)-(∫ y, g y ∂μ))| at hx
  rw [he'] at hx
  linarith

lemma sum_quadratic_exponential_bounds (C₁ C₂ q₁ q₂ : ℝ) (n : ℕ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    C₁*Real.exp (-q₁*(n : ℝ)^2)+C₂*Real.exp (-q₂*(n : ℝ)^2) ≤
      (C₁+C₂)*Real.exp (-(min q₁ q₂)*(n : ℝ)^2) := by
  have h1 : -q₁*(n : ℝ)^2 ≤ -(min q₁ q₂)*(n : ℝ)^2 :=
    mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) (sq_nonneg _)
  have h2 : -q₂*(n : ℝ)^2 ≤ -(min q₁ q₂)*(n : ℝ)^2 :=
    mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) (sq_nonneg _)
  calc
    _ ≤ C₁*Real.exp (-(min q₁ q₂)*(n : ℝ)^2)+
        C₂*Real.exp (-(min q₁ q₂)*(n : ℝ)^2) :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) hC₁)
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hC₂)
    _ = _ := by ring

#print axioms centered_difference_tail
#print axioms sum_quadratic_exponential_bounds
end SpectralRadiusUpperTail
