import SpectralRadiusUpperTail.OutlierProbability
import SpectralRadiusUpperTail.HSRightIsotropicTransfers
import SpectralRadiusUpperTail.RealHSRightDeformation
import SpectralRadiusUpperTail.AnnulusIsotropicProbabilityStability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix

lemma real_gaussianComparator_perturbed_isotropic_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℝ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℝ, z ∂μ) = 0) (hv : (∫ z : ℝ, ‖z‖^2 ∂μ) = 1)
    (v : ℕ → ℕ → ℝ) (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (t : (n : ℕ) → Fin n → ℝ)
    (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (C : ℝ) (hC : 0 < C)
    (hD : ∀ n, matrixHSsq (D n) ≤ C^2)
    (p : (n : ℕ) → Fin n → ℂ)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1)
    (E : (n : ℕ) → (Fin n → Fin n → ℝ × ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (herr : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      (gaussianSequentialMatrixLaw μ (v n) (a n) (t n)).real
      {x | δ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (E n x)‖}) atTop (𝓝 0))
    (r L ε : ℝ) (hr : 1 < r) (hL : 0 < L) (hε : 0 < ε) :
    Tendsto (fun n => (gaussianSequentialMatrixLaw μ (v n) (a n) (t n)).real
      {x | ¬ matrixAnnulusIsotropicControl
        (((normalizedArray (fun i => comparatorVector n (x i))).map Complex.ofRealHom)*(1+D n)+E n x)
        (p n) (p n) r L ε}) atTop (𝓝 0) := by
  have (n : ℕ) : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ (v n) (a n) (t n)) :=
    gaussianSequentialMatrixLaw_probability μ (v n) (a n) (ha n) (t n)
  obtain ⟨B,hB,hbaseIid⟩ := iid_real_HS_right_annulus_probability
    μ c hc hexp hm hv D C hC hD r L hr hL
  have hbase := squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => gaussianComparator_event_probability_le μ (v n) (a n) (ha n) (t n)
      (fun A => ¬ matrixAnnulusControl ((A.map Complex.ofRealHom)*(1+D n)) r L B)) hbaseIid
  have hiso : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (gaussianSequentialMatrixLaw μ (v n) (a n) (t n)).real
      {x | ¬ matrixAnnulusIsotropicControl
        (((normalizedArray (fun i => comparatorVector n (x i))).map Complex.ofRealHom)*(1+D n))
        (p n) (p n) r L ε}) atTop (𝓝 0) := by
    intro ε hε
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => gaussianComparator_event_probability_le μ (v n) (a n) (ha n) (t n)
        (fun A => ¬ matrixAnnulusIsotropicControl ((A.map Complex.ofRealHom)*(1+D n))
          (p n) (p n) r L ε))
      (iid_real_HS_right_isotropic_probability μ c hc hexp hm hv D C hC hD
        p p hp hp r L ε hr hL hε)
  exact annulus_isotropic_probability_stability
    (fun n => Fin n → Fin n → ℝ × ℝ)
    (fun n => gaussianSequentialMatrixLaw μ (v n) (a n) (t n))
    (fun n x => ((normalizedArray (fun i => comparatorVector n (x i))).map Complex.ofRealHom)*(1+D n))
    E p p hp hp r L B hB hbase
    hiso herr ε hε

#print axioms real_gaussianComparator_perturbed_isotropic_probability
end SpectralRadiusUpperTail
