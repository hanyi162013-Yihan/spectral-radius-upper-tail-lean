import SpectralRadiusUpperTail.ComplexHaarSquaredCoordinates

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal BigOperators

noncomputable def complexDiagonalSphereIntegral (n : ℕ) (c : ℝ) (h : Fin n → ℝ) : ℝ≥0∞ :=
  ∫⁻ v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1,
    ENNReal.ofReal (Real.exp (-c*∑ i, h i*‖v.val i‖^2))
    ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))

lemma complexDiagonalSphereIntegral_exponential (n : ℕ) (hn : 0 < n)
    (c : ℝ) (h : Fin n → ℝ) :
    complexDiagonalSphereIntegral n c h =
      ∫⁻ y : Fin n → ℝ, ENNReal.ofReal (Real.exp (-c*((∑ i, h i*y i)/(∑ i, y i))))
        ∂Measure.pi (fun _ => expMeasure (1/2)) := by
  let F : (Fin n → ℝ) → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-c*∑ i, h i*t i))
  have hF : Measurable F := by dsimp [F]; fun_prop
  have he := congrArg (fun ρ : Measure (Fin n → ℝ) => ∫⁻ t, F t ∂ρ)
    (complex_haar_squared_coordinates n hn)
  rw [lintegral_map hF (show Measurable
    (fun v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1 => fun i => ‖v.val i‖^2) by fun_prop),
    lintegral_map hF (show Measurable
      (fun y : Fin n → ℝ => fun i => y i/(∑ j, y j)) by fun_prop)] at he
  simpa only [complexDiagonalSphereIntegral, F, ← mul_div_assoc, ← Finset.sum_div] using he

#print axioms complexDiagonalSphereIntegral
#print axioms complexDiagonalSphereIntegral_exponential
end SpectralRadiusUpperTail
