import SpectralRadiusUpperTail.TalagrandCutoffProduct
import SpectralRadiusUpperTail.ComplexSharpClass
import SpectralRadiusUpperTail.RealSharpClass
import SpectralRadiusUpperTail.RealSharpFromInputs

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The bounded-product convex concentration assumption used by the
matrix applications is now a theorem for every real or complex entry law. -/
theorem cutoff_convex_concentration_proved
    {𝕂 : Type*} [RCLike 𝕂]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] :
    CutoffConvexConcentration μ :=
  cutoff_concentration_of_talagrand μ (cutoff_talagrand_hull_proved μ)

/-- The complex sharp matching class has the full clipped spectral-radius
open/closed large-deviation bounds with no concentration hypothesis. -/
theorem complex_sharp_class_clipped_deviation_bounds_of_entry_hypotheses
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (hp : (∫ z : ℂ, z^2 ∂μ) = 0)
    (hmgf : SharpPlanarMGF μ) :
    ClippedDeviationBounds (fun n => Fin n → Fin n → ℂ)
      (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
      (fun _ x => (spectralRadius ℂ (normalizedArray x)).toReal) 2 :=
  complex_sharp_class_clipped_deviation_bounds μ hm hv hp hmgf
    (cutoff_convex_concentration_proved μ)

/-- The real matching-class lower bound no longer requires a concentration
input. The real sharp upper bound is a separate Gaussian-power problem. -/
theorem real_class_matching_lower_of_entry_hypotheses
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ)
    (hvar : (∫ x : ℝ, x^2 ∂μ) = 1)
    (h : GaussianEvenMomentDomination μ)
    (r : ℝ) (hr : 1 < r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ)*(-rate 1 r-ε)) ≤
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ
          ((normalizedArray x).map Complex.ofRealHom)).toReal} :=
  real_class_matching_lower μ hsym hvar h r hr
    (cutoff_convex_concentration_proved μ) ε hε

/-- In the real full clipped theorem, the sole remaining explicit input is
the Gaussian matrix-power upper asymptotic. -/
theorem real_class_clipped_deviation_bounds_of_gaussian_power
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ)
    (hvar : (∫ x : ℝ, x^2 ∂μ) = 1)
    (h : GaussianEvenMomentDomination μ)
    (hG : GaussianPowerUpperInput) :
    ClippedDeviationBounds (fun n => Fin n → Fin n → ℝ)
      (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
      (fun _ x => (spectralRadius ℂ
        ((normalizedArray x).map Complex.ofRealHom)).toReal) 1 :=
  real_class_clipped_deviation_bounds μ hsym hvar h
    (cutoff_convex_concentration_proved μ) hG

#print axioms cutoff_convex_concentration_proved
#print axioms complex_sharp_class_clipped_deviation_bounds_of_entry_hypotheses
#print axioms real_class_matching_lower_of_entry_hypotheses
#print axioms real_class_clipped_deviation_bounds_of_gaussian_power
end SpectralRadiusUpperTail
