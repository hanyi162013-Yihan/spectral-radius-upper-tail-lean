import SpectralRadiusUpperTail.ClosedPatternDefectSum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
attribute [local instance] Classical.propDecidable

lemma gramPatternWeight_sum_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1)
    (m q n : ℕ) (hq : 1 ≤ q) :
    ∑ R : Setoid (Fin (2*(q*m)+1)), closedPatternWeight μ (gramTreeSign m q) n R ≤
      ∑ g : Fin (q*m+1), ((m+1 : ℝ)^(2*q) * (gramDefectCountBase m q : ℝ)^g.val) *
        ((n : ℝ)^(q*m+1-g.val) * (signedWordMomentBase μ c (2*(q*m)))^(6*g.val)) := by
  classical
  apply (closedPatternWeight_sum_le μ c hc hexp hm hv (gramTreeSign m q) n).trans
  apply Finset.sum_le_sum
  intro g _
  apply mul_le_mul_of_nonneg_right
  · have hh := closedGramDefectPattern_count_le μ hm m q hq g.val (by omega)
    exact_mod_cast hh
  · have ha := signedWordMomentBase_one_le μ c hc (2*(q*m))
    positivity

#print axioms gramPatternWeight_sum_le
end SpectralRadiusUpperTail
