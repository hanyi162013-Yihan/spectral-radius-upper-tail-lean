import SpectralRadiusUpperTail.ComplexBulkFromConvexConcentration
import SpectralRadiusUpperTail.RealConvexConcentrationTransfer
import SpectralRadiusUpperTail.RealBulkLogDetIdentity

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma real_bulk_concentration_of_convex_concentration
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h2 : Integrable (fun x : ℝ => ‖x‖^2) μ) (hconv : IidConvexConcentration μ)
    (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ b : ℝ,
        (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
          {x | δ < |regularizedResidualLogDet x b s/(n : ℝ)-
            ∫ y : Fin n → Fin n → ℝ, regularizedResidualLogDet y b s/(n : ℝ)
              ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))|} ≤ C*Real.exp (-q*(n : ℝ)^2) := by
  obtain ⟨C, hC, q, hq, ht⟩ := complex_bulk_concentration_of_convex_concentration (complexifiedLaw μ)
    (complexifiedLaw_second_integrable μ h2) (convex_concentration_complexifiedLaw μ hconv) s δ hs hδ
  refine ⟨C, hC, q, hq, ?_⟩
  filter_upwards [ht] with n hn b
  have he := centered_tail_map
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => complexifiedLaw μ)))
    (fun x : Fin n → Fin n → ℝ => fun i j => (x i j : ℂ)) (by fun_prop)
    (nested_iid_complexifiedLaw μ n)
    (fun x => regularizedResidualLogDet x (b : ℂ) s/(n : ℝ))
    ((regularizedResidualLogDet_measurable n (b : ℂ) s).div_const (n : ℝ)) δ
  simpa only [← regularizedResidualLogDet_complexify] using! he.trans_le (hn (b : ℂ))

#print axioms real_bulk_concentration_of_convex_concentration
end SpectralRadiusUpperTail
