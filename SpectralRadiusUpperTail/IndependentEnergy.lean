import SpectralRadiusUpperTail.Centering
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.Linarith

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

lemma inner_integrable_of_memLp_two (μ : Measure Ω) (X Y : Ω → E)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω => inner ℝ (X ω) (Y ω)) μ := by
  have hX2 := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX
  have hY2 := (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mp hY
  apply ((hX2.add hY2).div_const 2).mono'
    (hX.aestronglyMeasurable.inner hY.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  change ‖inner ℝ (X ω) (Y ω)‖ ≤ (‖X ω‖^2 + ‖Y ω‖^2)/2
  have hi := norm_inner_le_norm (𝕜 := ℝ) (X ω) (Y ω)
  nlinarith [sq_nonneg (‖X ω‖-‖Y ω‖)]

lemma independent_centered_inner_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → E) (hX : Integrable X μ) (hY : Integrable Y μ)
    (hi : IndepFun X Y μ) (hmean : (∫ ω, X ω ∂μ) = 0) :
    (∫ ω, inner ℝ (X ω) (Y ω) ∂μ) = 0 := by
  have h := hi.integral_bilin hX hY (innerSL ℝ (E := E))
  change (∫ ω, inner ℝ (X ω) (Y ω) ∂μ) = inner ℝ (∫ ω, X ω ∂μ) (∫ ω, Y ω ∂μ) at h
  simpa only [hmean, inner_zero_left] using h

/-- The actual second moment of a finite sum of independent centered vectors. -/
theorem independent_sum_norm_sq (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype ι] (X : ι → Ω → E) (hX : ∀ i, MemLp (X i) 2 μ)
    (hi : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0) :
    (∫ ω, ‖∑ i, X i ω‖^2 ∂μ) = ∑ i, ∫ ω, ‖X i ω‖^2 ∂μ := by
  classical
  have hint (i j : ι) := inner_integrable_of_memLp_two μ (X i) (X j) (hX i) (hX j)
  have hfun : (fun ω => ‖∑ i, X i ω‖^2) =
      fun ω => ∑ i, ∑ j, inner ℝ (X i ω) (X j ω) := by
    funext ω
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
  rw [hfun, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j), Finset.sum_eq_single i]
  · simp only [real_inner_self_eq_norm_sq]
  · intro j _ hji
    exact independent_centered_inner_integral μ (X i) (X j)
      ((hX i).integrable (by norm_num)) ((hX j).integrable (by norm_num))
      (hi hji.symm) (hmean i)
  · simp

#print axioms independent_sum_norm_sq
end SpectralRadiusUpperTail
