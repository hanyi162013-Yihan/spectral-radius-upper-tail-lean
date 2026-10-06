import SpectralRadiusUpperTail.GaussianMoments
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory WithLp

/-- Any Euclidean linear isometry preserves a finite product of standard
real Gaussian coordinates, after identifying the coordinate array with
Euclidean space. This is the rotation-invariance input for a future
real-Schur change of variables. -/
theorem gaussianProductLaw_map_euclidean_isometry
    {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (Measure.pi (fun _ : ι => standardNormal)).map
      (fun x : ι → ℝ => ofLp (U (toLp 2 x))) =
      Measure.pi (fun _ : ι => standardNormal) := by
  let μ : Measure (ι → ℝ) := Measure.pi (fun _ => standardNormal)
  have hTo : μ.map (toLp 2) = stdGaussian (EuclideanSpace ℝ ι) := by
    simpa [μ, standardNormal] using
      (map_pi_eq_stdGaussian (ι := ι))
  have hOf : Measurable (fun y : EuclideanSpace ℝ ι => ofLp y) := by
    fun_prop
  have hToMeas : Measurable (fun x : ι → ℝ => toLp 2 x) := by
    fun_prop
  have hU : Measurable (fun y : EuclideanSpace ℝ ι => U y) :=
    U.continuous.measurable
  change μ.map (fun x : ι → ℝ => ofLp (U (toLp 2 x))) = μ
  calc
    μ.map (fun x : ι → ℝ => ofLp (U (toLp 2 x))) =
        (μ.map (toLp 2)).map (fun y => ofLp (U y)) := by
      simpa only [Function.comp_def] using
        (Measure.map_map (hOf.comp hU) hToMeas).symm
    _ = ((μ.map (toLp 2)).map U).map (fun y => ofLp y) := by
      simpa only [Function.comp_def] using
        (Measure.map_map hOf hU).symm
    _ = (stdGaussian (EuclideanSpace ℝ ι)).map
        (fun y => ofLp y) := by
      rw [hTo, stdGaussian_map]
    _ = μ := by
      rw [← hTo, Measure.map_map hOf hToMeas]
      have heq : ((fun y : EuclideanSpace ℝ ι => ofLp y) ∘
          (toLp 2)) = (id : (ι → ℝ) → (ι → ℝ)) := by
        funext x
        exact ofLp_toLp 2 x
      rw [heq, Measure.map_id]

#print axioms gaussianProductLaw_map_euclidean_isometry
end SpectralRadiusUpperTail
