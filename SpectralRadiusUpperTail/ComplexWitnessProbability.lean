import SpectralRadiusUpperTail.ComplexWitnessMarkov

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

lemma complex_witness_probability_bound (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u)
    (z : ℂ) (d L : ℝ) (P : Measure (Fin n → Fin n → ℂ)) :
    P (complexApproximateBulkEvent n u z d L) ≤
      (ENNReal.ofReal (Real.exp ((n : ℝ)*(Real.log u-1-d/u-L))))⁻¹*
        ∫⁻ x, fullSpectralSphereWeight n u z x ∂P := by
  let c := ENNReal.ofReal (Real.exp ((n : ℝ)*(Real.log u-1-d/u-L)))
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hh := mul_le_mul' (le_refl c⁻¹) (complex_witness_markov n hn u hu z d L P)
  change c⁻¹*(c*P (complexApproximateBulkEvent n u z d L)) ≤ _ at hh
  rw [ENNReal.inv_mul_cancel_left hc ENNReal.ofReal_ne_top] at hh
  exact hh

#print axioms complex_witness_probability_bound
end SpectralRadiusUpperTail
