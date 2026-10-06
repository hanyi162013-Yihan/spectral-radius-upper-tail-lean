import SpectralRadiusUpperTail.OutlierProbability
import SpectralRadiusUpperTail.HSRightIsotropicTransfers
import SpectralRadiusUpperTail.GaussianComparatorHSRight
import SpectralRadiusUpperTail.AnnulusIsotropicProbabilityStability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix

lemma gaussianComparator_perturbed_outlier_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (v : ℕ → ℕ → ℂ) (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (t : (n : ℕ) → Fin n → ℂ)
    (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (C : ℝ) (hC : 0 < C)
    (hD : ∀ n, matrixHSsq (D n) ≤ C^2)
    (p : (n : ℕ) → Fin n → ℂ)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1)
    (hunit : ∀ n, 0 < n → (∑ i, ‖p n i‖^2) = 1)
    (E : (n : ℕ) → (Fin n → Fin n → ℂ × ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (herr : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      (gaussianSequentialMatrixLaw μ (v n) (a n) (t n)).real
      {x | δ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (E n x)‖}) atTop (𝓝 0))
    (b : ℂ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖b‖-1) :
    Tendsto (fun n => (gaussianSequentialMatrixLaw μ (v n) (a n) (t n)).real
      {x | ¬ ∃ z ∈ closedBall b d, z ∈ spectrum ℂ
        ((normalizedArray (fun i => comparatorVector n (x i)))*(1+D n)+E n x+
          b • Matrix.vecMulVec (p n) (star (p n)))}) atTop (𝓝 0) := by
  have (n : ℕ) : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ (v n) (a n) (t n)) :=
    gaussianSequentialMatrixLaw_probability μ (v n) (a n) (ha n) (t n)
  apply outlier_probability_of_annulus_isotropic
    (fun n => Fin n → Fin n → ℂ × ℂ)
    (fun n => gaussianSequentialMatrixLaw μ (v n) (a n) (t n))
    (fun n x => (normalizedArray (fun i => comparatorVector n (x i)))*(1+D n)+E n x)
    p hunit b d hd hgap
  intro r L ε hr hL hε
  obtain ⟨B,hB,hbase⟩ := gaussianComparator_HS_right_annulus_probability
    μ c hc hexp hm hv v a ha t D C hC hD r L hr hL
  exact annulus_isotropic_probability_stability
    (fun n => Fin n → Fin n → ℂ × ℂ)
    (fun n => gaussianSequentialMatrixLaw μ (v n) (a n) (t n))
    (fun n x => (normalizedArray (fun i => comparatorVector n (x i)))*(1+D n))
    E p p hp hp r L B hB hbase
    (fun ε hε => gaussianComparator_HS_right_isotropic_probability
      μ c hc hexp hm hv v a ha t D C hC hD p p hp hp r L ε hr hL hε)
    herr ε hε

#print axioms gaussianComparator_perturbed_outlier_probability
end SpectralRadiusUpperTail
