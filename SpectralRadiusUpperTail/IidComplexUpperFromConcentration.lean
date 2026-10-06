import SpectralRadiusUpperTail.IidComplexUpperConditional
import SpectralRadiusUpperTail.IidComplexOpNormExponentialTightness

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Actual iid upper bound with the norm tail and exterior bulk mean proved.
Only centered concentration and the full-sphere annealed estimate remain as inputs. -/
lemma iid_complex_upper_of_concentration_annealed
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (r : ℝ) (hr : 1 < r)
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
  have hXi : Integrable (fun x : ℂ => x) μ := by
    apply (squareExp_norm_pow_integrable μ c hc hexp 1).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun x => by simp)
  apply iid_complex_upper_of_concentration_annealed_norm μ c hc hexp hm hv r hr
    ?_ hconc hannealed ε hε
  intro K hK
  exact iid_complex_opNorm_exponential_tightness μ hXi hm c hc hexp r K hK

#print axioms iid_complex_upper_of_concentration_annealed
end SpectralRadiusUpperTail
