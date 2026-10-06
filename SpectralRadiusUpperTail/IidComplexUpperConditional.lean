import SpectralRadiusUpperTail.ComplexUpperFromThreeInputs
import SpectralRadiusUpperTail.ComplexBulkUpperFromConcentration

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology ENNReal

/-- The iid exterior mean and all deterministic witness steps are discharged.
The remaining inputs are centered concentration, annealed control and a norm tail. -/
lemma iid_complex_upper_of_concentration_annealed_norm
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (r : ℝ) (hr : 1 < r)
    (hnorm : ∀ K : ℝ, 0 < K → ∃ R : ℝ, r < R ∧ ∀ᶠ n : ℕ in atTop,
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real {x | R < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖} ≤ Real.exp (-K*(n : ℝ)))
    (hconc : ∀ R s δ : ℝ, 0 < s → 0 < δ →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
          (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
            {x | δ < |regularizedResidualLogDet x z s/(n : ℝ)-
              ∫ y : Fin n → Fin n → ℂ, regularizedResidualLogDet y z s/(n : ℝ)
                ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))|} ≤ C*Real.exp (-q*(n : ℝ)^2))
    (hannealed : ∀ R u ε : ℝ, 0 < u → 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
        (∫⁻ x, fullSpectralSphereWeight n u z x ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) ≤
          ENNReal.ofReal (Real.exp ((n : ℝ)*(complexAnnealedExponent u ‖z‖+ε))))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r ≤ (spectralRadius ℂ (normalizedArray x)).toReal} ≤
          Real.exp ((n : ℝ)*(-rate 2 r+ε)) := by
  obtain ⟨M, hM, hbulk⟩ := complex_bulk_upper_of_concentration μ c hc hexp hm hv r hr hconc
  apply complex_upper_from_three_inputs
    (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) r hr
    hnorm ?_ hannealed ε hε
  refine ⟨M, hM, ?_⟩
  intro R u δ hu hδ
  simpa only [mul_assoc] using hbulk R (2*u) δ (by positivity) hδ

#print axioms iid_complex_upper_of_concentration_annealed_norm
end SpectralRadiusUpperTail
