import SpectralRadiusUpperTail.FiniteOrthogonalSecondMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma finite_sum_cross_orthogonality {ι κ Ω : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] (μ : Measure Ω) (F : ι → Ω → ℝ) (G : κ → Ω → ℝ)
    (hi : ∀ i j, Integrable (fun x => F i x*G j x) μ)
    (hz : ∀ i j, (∫ x, F i x*G j x ∂μ) = 0) :
    Integrable (fun x => (∑ i, F i x)*(∑ j, G j x)) μ ∧
    (∫ x, (∑ i, F i x)*(∑ j, G j x) ∂μ) = 0 := by
  classical
  simp_rw [Finset.sum_mul_sum]
  constructor
  · exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))
  · rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hi _ j), hz]
    simp

#print axioms finite_sum_cross_orthogonality
end SpectralRadiusUpperTail
