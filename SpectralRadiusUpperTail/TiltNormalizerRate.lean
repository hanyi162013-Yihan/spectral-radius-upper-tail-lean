import SpectralRadiusUpperTail.TiltCostAlgebra
import SpectralRadiusUpperTail.ComplexJointTiltNormalizer
import SpectralRadiusUpperTail.RealJointTiltNormalizer

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma complex_tilt_rate_identity (b u : ℝ) :
    Real.log (u/(u+1))-‖(b : ℂ)‖^2/(u+1) = annealedTiltRate 2 b u := by
  simp only [annealedTiltRate,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  ring

lemma real_tilt_rate_identity (b u : ℝ) (hu : 0 < u) :
    Real.log (Real.sqrt (2*u/(2*u+2)))-b^2/(2*u+2) = annealedTiltRate 1 b u := by
  have he : 2*u/(2*u+2) = u/(1+u) := by
    field_simp
    <;> ring
  have hd : b^2/(2*u+2) = (b^2/(1+u))/2 := by
    field_simp
    <;> ring
  rw [he,hd,Real.log_sqrt (by positivity)]
  unfold annealedTiltRate
  ring

lemma complex_manuscript_annealed_limit (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (c*‖x‖^2)) μ)
    (u : ℝ) (hu : 0 < u) (L : ℝ) (hL : 0 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℂ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℝ) :
    Tendsto (fun n => Real.log (∫ p, flatSpectralJointWeight u (b : ℂ) p
      ∂(ν n).prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))))/(n : ℝ))
      atTop (𝓝 (annealedTiltRate 2 b u)) := by
  rw [← complex_tilt_rate_identity]
  exact complex_joint_spectralTilt_logNormalizer_limit μ hm hvar hpseudo c hc hexp u hu L hL ν b

lemma real_manuscript_annealed_limit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ)
    (u : ℝ) (hu : 0 < u) (L : ℝ) (hL : 0 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℝ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℝ) :
    Tendsto (fun n => Real.log (∫ p, flatSpectralJointWeight (2*u) b p
      ∂(ν n).prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))))/(n : ℝ))
      atTop (𝓝 (annealedTiltRate 1 b u)) := by
  rw [← real_tilt_rate_identity b u hu]
  exact real_joint_spectralTilt_logNormalizer_limit μ hm hvar c hc hexp (2*u) (by positivity) L hL ν b

#print axioms complex_tilt_rate_identity
#print axioms real_tilt_rate_identity
#print axioms complex_manuscript_annealed_limit
#print axioms real_manuscript_annealed_limit
end SpectralRadiusUpperTail
