import SpectralRadiusUpperTail.IidComplexUpperFromConcentration
import SpectralRadiusUpperTail.ComplexFullSphereAnnealedBound

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Every upper-bound input except centered bulk concentration is discharged. -/
lemma complex_sharp_upper_of_concentration (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (hp : (∫ z : ℂ, z^2 ∂μ) = 0)
    (hint : ∀ u : ℂ, Integrable (fun x : ℂ => Real.exp (2*(star u*x).re)) μ)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (r : ℝ) (hr : 1 < r)
    (hconc : ∀ R s δ : ℝ, 0 < s → 0 < δ →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
          (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
            {x | δ < |regularizedResidualLogDet x z s/(n : ℝ)-
              ∫ y : Fin n → Fin n → ℂ, regularizedResidualLogDet y z s/(n : ℝ)
                ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))|} ≤ C*Real.exp (-q*(n : ℝ)^2))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r ≤ (spectralRadius ℂ (normalizedArray x)).toReal} ≤
          Real.exp ((n : ℝ)*(-rate 2 r+ε)) := by
  have hX : MemLp (fun x : ℂ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ c hc hexp 2)
  apply iid_complex_upper_of_concentration_annealed μ c hc hexp hm hv r hr hconc ?_ ε hε
  intro R a δ ha hδ
  filter_upwards [complex_fullSphere_annealed_bound μ hX hm hv hp
    (squareExp_norm_pow_integrable μ c hc hexp 3) hint hmgf R a δ ha hδ] with n hn z _ hzR
  exact hn z hzR

#print axioms complex_sharp_upper_of_concentration
end SpectralRadiusUpperTail
