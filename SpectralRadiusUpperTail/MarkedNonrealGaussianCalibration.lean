import SpectralRadiusUpperTail.MarkedNonrealGaussianExpectation
import SpectralRadiusUpperTail.MarkedNonrealDiagonalEvaluation

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

theorem MarkedNonrealFlagAtlas.expectation_eq_pairTest
    {m : ℕ} {hm : 0 < m} (F : MarkedNonrealFlagAtlas m hm)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ a : MarkedNonrealIndex m × MarkedNonrealIndex m → ℝ,
      markedNonrealRootWeight m (Matrix.of a.curry) g
        ∂Measure.pi (fun _ => standardNormal)) =
      (F.coefficient*markedNonrealComplementMass m)*markedNonrealPairTestIntegral m g := by
  rw [F.gaussian_expectation g hg,markedNonrealDiagonalIntegral_eq_pairTest m g hg,mul_assoc]

/-- Total root count calibrates the angular constant. No exact volume
formula for the Grassmannian is needed for this polynomial upper bound. -/
theorem MarkedNonrealFlagAtlas.coefficient_bound
    {m : ℕ} {hm : 0 < m} (F : MarkedNonrealFlagAtlas m hm) :
    F.coefficient*markedNonrealComplementMass m ≤ (m+2 : ℕ)/markedNonrealPairReferenceMass := by
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl markedNonrealPairReferenceMass_pos.ne')
    (Or.inl markedNonrealPairReferenceMass_ne_top)).mpr
  calc
    _ ≤ (F.coefficient*markedNonrealComplementMass m)*
        markedNonrealPairTestIntegral m (fun _ => 1) :=
      mul_le_mul le_rfl (markedNonrealPairReferenceMass_le_testIntegral m) zero_le zero_le
    _ = ∫⁻ a : MarkedNonrealIndex m × MarkedNonrealIndex m → ℝ,
        markedNonrealRootWeight m (Matrix.of a.curry) (fun _ => 1)
          ∂Measure.pi (fun _ => standardNormal) :=
      (F.expectation_eq_pairTest (fun _ => 1) measurable_const).symm
    _ ≤ _ := markedNonrealRootWeight_expectation_one_le m

/-- Actual nonreal weighted counts are bounded by the explicit pair
integral with only a linear dimension factor and a fixed positive constant. -/
theorem markedNonrealGaussian_weighted_upper
    (m : ℕ) (hm : 0 < m) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ a : MarkedNonrealIndex m × MarkedNonrealIndex m → ℝ,
      markedNonrealRootWeight m (Matrix.of a.curry) g
        ∂Measure.pi (fun _ => standardNormal)) ≤
      ((m+2 : ℕ)/markedNonrealPairReferenceMass)*markedNonrealPairTestIntegral m g := by
  obtain ⟨F⟩ := exists_markedNonrealFlagAtlas m hm
  rw [F.expectation_eq_pairTest g hg]
  exact mul_le_mul F.coefficient_bound le_rfl zero_le zero_le

#print axioms MarkedNonrealFlagAtlas.expectation_eq_pairTest
#print axioms MarkedNonrealFlagAtlas.coefficient_bound
#print axioms markedNonrealGaussian_weighted_upper
end SpectralRadiusUpperTail
