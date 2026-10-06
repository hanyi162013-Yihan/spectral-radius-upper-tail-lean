import SpectralRadiusUpperTail.GaussianRowRegression

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

lemma flat_future_cube_sum (v : ℕ → 𝕂) (j : Fin N) (δ : ℝ)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1) (hflat : ∀ i : Fin N, ‖v i.val‖ ≤ δ) :
    ‖v j.val‖ ≤ 1 ∧ (∑ i : Fin j.val, ‖v i.val‖^3) ≤ δ := by
  have he := current_future_energy v j hv
  have hq : 0 ≤ ∑ i : Fin j.val, ‖v i.val‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hq1 : (∑ i : Fin j.val, ‖v i.val‖^2) ≤ 1 := by nlinarith [sq_nonneg ‖v j.val‖]
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hflat j)
  refine ⟨by nlinarith [norm_nonneg (v j.val)], ?_⟩
  calc
    _ ≤ ∑ i : Fin j.val, δ*‖v i.val‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hflat ⟨i.val, by omega⟩
      have hh := mul_le_mul_of_nonneg_right hi (sq_nonneg ‖v i.val‖)
      nlinarith only [hh]
    _ = δ*(∑ i : Fin j.val, ‖v i.val‖^2) := (Finset.mul_sum _ _ _).symm
    _ ≤ δ*1 := mul_le_mul_of_nonneg_left hq1 hδ
    _ = δ := mul_one _

/-- A scalar bookkeeping lemma for the compact regression estimate. -/
lemma compact_regression_flat_bound (r b q A B D δ : ℝ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hbδ : b ≤ δ) (hq : q ≤ δ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hr : r ≤ A*b^2+B*b*q+D*b^3) :
    r ≤ (A+B+D)*δ*b := by
  have hb2 : b^2 ≤ δ*b := by nlinarith [mul_le_mul_of_nonneg_right hbδ hb]
  have hb3 : b^3 ≤ δ*b := by
    have hh := mul_le_mul_of_nonneg_right hb1 (sq_nonneg b)
    nlinarith only [hh, hb2]
  have ha := mul_le_mul_of_nonneg_left hb2 hA
  have hbb := mul_le_mul_of_nonneg_left hq (mul_nonneg hB hb)
  have hdd := mul_le_mul_of_nonneg_left hb3 hD
  nlinarith only [hr, ha, hbb, hdd]

lemma gaussianEntryTaylorConstant_nonneg (a R σ m : ℝ) (ha : 0 < a) (hm : 0 ≤ m) :
    0 ≤ gaussianEntryTaylorConstant a R σ m := by
  unfold gaussianEntryTaylorConstant
  positivity

lemma gaussianScoreComparisonConstant_nonneg (a R : ℝ) (ha : 0 < a) :
    0 ≤ gaussianScoreComparisonConstant a R := by
  have h1 := gaussianDirectionalThirdConstant_nonneg a ha
  have h2 := gaussianThirdConstant_nonneg a ha
  unfold gaussianScoreComparisonConstant
  positivity

/-- On every compact target set, the actual real row residual is bounded by
an explicit dimension-free constant times the maximum and current coefficients. -/
theorem real_gaussianRowRegression_flat_compact (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (τ : ℝ) (hτ : 0 < τ) (hexp : Integrable (fun x : ℝ => Real.exp (τ*‖x‖^2)) μ)
    (v : ℕ → ℝ) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (δ : ℝ) (hflat : ∀ i : Fin N, ‖v i.val‖ ≤ δ)
    (j : Fin N) (t : ℝ) (η : ℝ) (hη : 0 < η) (R : ℝ) (hR : 0 ≤ R) (x : Fin N → ℝ)
    (hx : ‖upperRowTarget v j t x‖ ≤ R) :
    ‖gaussianRowRegression μ (2*η) v j t η x‖ ≤
      (gaussianEntryTaylorConstant (2*η) R 1 (∫ z : ℝ, ‖z‖^3 ∂μ)+
        gaussianScoreComparisonConstant (2*η) R*
          ((∫ z : ℝ, ‖z‖^3 ∂μ)+(∫ z : ℝ, ‖z‖^3 ∂standardNormal))+R/η^2)*δ*‖v j.val‖ := by
  have hcube := flat_future_cube_sum v j δ hv hflat
  have h3 : 0 ≤ ∫ z : ℝ, ‖z‖^3 ∂μ := integral_nonneg (fun _ => by positivity)
  have h3G : 0 ≤ ∫ z : ℝ, ‖z‖^3 ∂standardNormal := integral_nonneg (fun _ => by positivity)
  apply compact_regression_flat_bound _ ‖v j.val‖ (∑ i : Fin j.val, ‖v i.val‖^3) _ _ _ δ
    (norm_nonneg _) hcube.1 (hflat j) hcube.2
    (gaussianEntryTaylorConstant_nonneg _ _ _ _ (by positivity) h3)
    (mul_nonneg (gaussianScoreComparisonConstant_nonneg _ _ (by positivity)) (add_nonneg h3 h3G))
    (div_nonneg hR (sq_nonneg _))
  have hh := real_gaussianRowRegression_compact μ hm hvar τ hτ hexp v hv j t η hη R x hx
  have hs := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hx (sq_nonneg η))
    (pow_nonneg (norm_nonneg (v j.val)) 3)
  nlinarith only [hh, hs]

/-- The same flat compact estimate holds for proper complex entries. -/
theorem complex_gaussianRowRegression_flat_compact (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (τ : ℝ) (hτ : 0 < τ) (hexp : Integrable (fun x : ℂ => Real.exp (τ*‖x‖^2)) μ)
    (v : ℕ → ℂ) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (δ : ℝ) (hflat : ∀ i : Fin N, ‖v i.val‖ ≤ δ)
    (j : Fin N) (t : ℂ) (η : ℝ) (hη : 0 < η) (R : ℝ) (hR : 0 ≤ R) (x : Fin N → ℂ)
    (hx : ‖upperRowTarget v j t x‖ ≤ R) :
    ‖gaussianRowRegression μ η v j t η x‖ ≤
      (gaussianEntryTaylorConstant η R (1/2) (∫ z : ℂ, ‖z‖^3 ∂μ)+
        ((1/2)*gaussianScoreComparisonConstant η R)*
          ((∫ z : ℂ, ‖z‖^3 ∂μ)+(∫ z : ℂ, ‖z‖^3 ∂properComplexGaussian))+R/η^2)*δ*‖v j.val‖ := by
  have hcube := flat_future_cube_sum v j δ hv hflat
  have h3 : 0 ≤ ∫ z : ℂ, ‖z‖^3 ∂μ := integral_nonneg (fun _ => by positivity)
  have h3G : 0 ≤ ∫ z : ℂ, ‖z‖^3 ∂properComplexGaussian := integral_nonneg (fun _ => by positivity)
  apply compact_regression_flat_bound _ ‖v j.val‖ (∑ i : Fin j.val, ‖v i.val‖^3) _ _ _ δ
    (norm_nonneg _) hcube.1 (hflat j) hcube.2
    (gaussianEntryTaylorConstant_nonneg _ _ _ _ hη h3)
    (mul_nonneg (mul_nonneg (by norm_num) (gaussianScoreComparisonConstant_nonneg _ _ hη))
      (add_nonneg h3 h3G)) (div_nonneg hR (sq_nonneg _))
  have hh := complex_gaussianRowRegression_compact μ hm hvar hpseudo τ hτ hexp v hv j t η hη R x hx
  have hs := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hx (sq_nonneg η))
    (pow_nonneg (norm_nonneg (v j.val)) 3)
  nlinarith only [hh, hs]

#print axioms flat_future_cube_sum
#print axioms real_gaussianRowRegression_flat_compact
#print axioms complex_gaussianRowRegression_flat_compact
end SpectralRadiusUpperTail
