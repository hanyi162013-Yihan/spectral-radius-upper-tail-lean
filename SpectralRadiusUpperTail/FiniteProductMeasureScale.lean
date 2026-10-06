import Mathlib.MeasureTheory.Constructions.Pi

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

/-- Finite scalar factors can be collected outside a finite product of
finite measures, including zero factors. -/
theorem finite_pi_measure_smul {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : ι → Measure E) [∀ i, IsFiniteMeasure (μ i)]
    (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ∞) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  let : ∀ i, IsFiniteMeasure (c i • μ i) := fun i =>
    ⟨by
      rw [Measure.smul_apply,smul_eq_mul]
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (hc i)) (measure_lt_top (μ i) Set.univ)⟩
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply,smul_eq_mul,Measure.pi_pi]
  simp only [Measure.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]

#print axioms finite_pi_measure_smul
end SpectralRadiusUpperTail
