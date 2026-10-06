import SpectralRadiusUpperTail.MatrixRootCountSignSymmetry
import SpectralRadiusUpperTail.GaussianMatrixSignSymmetry
import SpectralRadiusUpperTail.RealGaussianRadiusConditional
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

theorem realGaussianPositiveRootCount_neg (n : ℕ) (r : ℝ)
    (x : (Fin n × Fin n) → ℝ) :
    realGaussianExteriorCount n r 0 (-x) =
      realGaussianExteriorCount n r 1 x := by
  have hmatrix :
      (((1/Real.sqrt (n : ℝ)) • entryMatrix (-x)).map Complex.ofRealHom) =
        -(((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom) := by
    ext i j
    simp [entryMatrix, Matrix.smul_apply, Matrix.map_apply]
  simp only [realGaussianExteriorCount, matrixExteriorRootCount,
    ↓reduceIte]
  rw [hmatrix, matrixPositiveRealRootCount_neg]
  simp

theorem realGaussianNegativeRootCount_measurable (n : ℕ) (r : ℝ)
    (hPos : Measurable (realGaussianExteriorCount n r 0)) :
    Measurable (realGaussianExteriorCount n r 1) := by
  have heq : realGaussianExteriorCount n r 1 =
      (fun x : (Fin n × Fin n) → ℝ =>
        realGaussianExteriorCount n r 0 (-x)) := by
    funext x
    exact (realGaussianPositiveRootCount_neg n r x).symm
  rw [heq]
  exact hPos.comp (by fun_prop)

theorem realGaussianRealRootCountExpectations_equal (n : ℕ) (r : ℝ)
    (hPos : Measurable (realGaussianExteriorCount n r 0)) :
    (∫ x, realGaussianExteriorCount n r 1 x ∂gaussianMatrixLaw n) =
    (∫ x, realGaussianExteriorCount n r 0 x ∂gaussianMatrixLaw n) := by
  let μ := gaussianMatrixLaw n
  have hmap : μ.map (fun x : (Fin n × Fin n) → ℝ => -x) = μ :=
    gaussianMatrixLaw_map_neg n
  have hPosMap : AEStronglyMeasurable
      (realGaussianExteriorCount n r 0)
      (μ.map (fun x : (Fin n × Fin n) → ℝ => -x)) := by
    rw [hmap]
    exact hPos.aestronglyMeasurable
  calc
    (∫ x, realGaussianExteriorCount n r 1 x ∂μ) =
        ∫ x, realGaussianExteriorCount n r 0 (-x) ∂μ := by
      congr 1
      funext x
      exact (realGaussianPositiveRootCount_neg n r x).symm
    _ = ∫ x, realGaussianExteriorCount n r 0 x
        ∂(μ.map (fun x : (Fin n × Fin n) → ℝ => -x)) := by
      exact (integral_map (by fun_prop) hPosMap).symm
    _ = _ := by rw [hmap]

/-- Only the positive-real and nonreal one-point inputs are needed for the
independent real Gaussian radius right-tail theorem: Gaussian sign symmetry
supplies the negative-real branch. -/
theorem real_gaussian_radius_rate_of_two_one_point_classes
    (r : ℝ) (hr : 1 < r)
    (hMeasPos : ∀ n, Measurable (realGaussianExteriorCount n r 0))
    (hMeasNon : ∀ n, Measurable (realGaussianExteriorCount n r 2))
    (hPos : ∀ n, 3 ≤ n →
      (∫ x, realGaussianExteriorCount n r 0 x ∂gaussianMatrixLaw n) =
        realGinibreRealPositiveTailMass n r)
    (hNonreal : ∀ n, 3 ≤ n →
      (∫ x, realGaussianExteriorCount n r 2 x ∂gaussianMatrixLaw n) ≤
        2*realGinibreNonrealExteriorMass n r) :
    Tendsto (fun n : ℕ => Real.log ((gaussianMatrixLaw n).real
      {x | r < realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix x)}) /
      (n : ℝ)) atTop (𝓝 (-rate 1 r)) := by
  apply real_gaussian_radius_rate_of_one_point_identities r hr
  · intro n i
    fin_cases i
    · exact hMeasPos n
    · exact realGaussianNegativeRootCount_measurable n r (hMeasPos n)
    · exact hMeasNon n
  · exact hPos
  · intro n hn
    rw [realGaussianRealRootCountExpectations_equal n r (hMeasPos n)]
    exact hPos n hn
  · exact hNonreal

#print axioms realGaussianPositiveRootCount_neg
#print axioms realGaussianNegativeRootCount_measurable
#print axioms realGaussianRealRootCountExpectations_equal
#print axioms real_gaussian_radius_rate_of_two_one_point_classes
end SpectralRadiusUpperTail
