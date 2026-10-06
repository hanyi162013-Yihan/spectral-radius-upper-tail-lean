import SpectralRadiusUpperTail.ComplexWitnessBulkEvent
import SpectralRadiusUpperTail.FullSphereWeightMeasurable

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

noncomputable def complexApproximateBulkEvent (n : ℕ) (u : ℝ) (z : ℂ) (d L : ℝ) :
    Set (Fin n → Fin n → ℂ) :=
  {x | (∃ v : EuclideanSpace ℂ (Fin n), ‖v‖ = 1 ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x-z • 1) v‖^2 ≤ d) ∧
      regularizedResidualLogDet x z (2*u)/(n : ℝ) ≤ L}

lemma complex_witness_markov (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u)
    (z : ℂ) (d L : ℝ) (P : Measure (Fin n → Fin n → ℂ)) :
    ENNReal.ofReal (Real.exp ((n : ℝ)*(Real.log u-1-d/u-L)))*
      P (complexApproximateBulkEvent n u z d L) ≤
        ∫⁻ x, fullSpectralSphereWeight n u z x ∂P := by
  have hset : complexApproximateBulkEvent n u z d L ⊆
      {x | ENNReal.ofReal (Real.exp ((n : ℝ)*(Real.log u-1-d/u-L))) ≤ fullSpectralSphereWeight n u z x} := by
    intro x hx
    obtain ⟨⟨v, hv, hd⟩, hb⟩ := hx
    exact complex_witness_on_bulk_event n hn u hu x z v hv d L hd hb
  exact (mul_le_mul' le_rfl (measure_mono hset)).trans
    (mul_meas_ge_le_lintegral (fullSpectralSphereWeight_measurable n hn u z) _)

#print axioms complexApproximateBulkEvent
#print axioms complex_witness_markov
end SpectralRadiusUpperTail
