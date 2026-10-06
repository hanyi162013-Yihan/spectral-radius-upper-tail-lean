import SpectralRadiusUpperTail.GaussianComparatorOutlier
import SpectralRadiusUpperTail.DescendingHSBudget
import SpectralRadiusUpperTail.RankOneTargetBound
import SpectralRadiusUpperTail.SequentialMatrixApproximation

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix

lemma complex_tilted_outlier_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (η L : ℝ) (hη : 0 < η) (hL : 0 ≤ L)
    (v : ℕ → ℕ → ℂ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hunit : ∀ n, 0 < n → (∑ j : Fin n, ‖v n j.val‖^2) = 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (b : ℂ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖b‖-1) :
    Tendsto (fun n => (gaussianSequentialMatrixLaw μ (v n) η (rankOneTiltTarget η b (v n))).real
      {x | ¬ ∃ z ∈ closedBall b d, z ∈ spectrum ℂ
        (normalizedArray (fun i => coordinateVector Prod.fst n (x i)))}) atTop (𝓝 0) := by
  let p := fun n (i : Fin n) => v n i.val
  let t : (n : ℕ) → Fin n → ℂ := fun n => rankOneTiltTarget η b (v n)
  let D := fun n => descendingTriangularInverse η (p n)-1
  let E := fun n (x : Fin n → Fin n → ℂ × ℂ) =>
    normalizedArray (fun i => coordinateVector Prod.fst n (x i)) -
      (normalizedArray (fun i => comparatorVector n (x i))*
        descendingTriangularInverse η (p n)+gaussianMeanMatrix (v n) (t n) η)
  have herr := complex_sequential_matrix_approximation μ hm hvar hpseudo c hc hexp
    η ((η+1)*‖b‖*L) L hη hL v hv hunit hflat t
    (fun n i => rankOneTiltTarget_bound η hη b (v n) L (hflat n) i)
  have ht := gaussianComparator_perturbed_outlier_probability μ (4*c) (by positivity)
    hexp hm hvar v (fun _ => η) (fun _ => hη) t D
    (1+Real.sqrt (1/(2*η^2))) (by positivity)
    (descendingTriangular_HS_budget η hη p hunit) p hv hunit E herr b d hd hgap
  have (n : ℕ) : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ (v n) η (t n)) :=
    gaussianSequentialMatrixLaw_probability μ (v n) η hη (t n)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ ht
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  letI := gaussianSequentialMatrixLaw_probability μ (v n) η hη (rankOneTiltTarget (n := n) η b (v n))
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx hz
  apply hx
  have he : normalizedArray (fun i => comparatorVector n (x i))*(1+D n)+E n x+
      b • Matrix.vecMulVec (p n) (star (p n)) =
        normalizedArray (fun i => coordinateVector Prod.fst n (x i)) := by
    dsimp [D,E]
    rw [gaussianMeanMatrix_rankOne η hη b (v n) (by omega) (hunit n (by omega))]
    simp only [p,t,add_sub_cancel_left]
    abel
  rwa [he] at hz

#print axioms complex_tilted_outlier_probability
end SpectralRadiusUpperTail
