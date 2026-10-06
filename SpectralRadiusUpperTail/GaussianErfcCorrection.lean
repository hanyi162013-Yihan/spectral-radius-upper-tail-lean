import SpectralRadiusUpperTail.GaussianErfcEnvelope
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- The dimensionless erfc factor in the nonreal real-Ginibre density. -/
noncomputable def gaussianErfcCorrection (t : ℝ) : ℝ :=
  Real.sqrt Real.pi * t * Real.exp (t^2) * gaussianErfc t

theorem gaussianErfc_nonneg (t : ℝ) : 0 ≤ gaussianErfc t := by
  unfold gaussianErfc
  have hint : 0 ≤ (∫ x : ℝ in Ioi t, Real.exp (-x^2)) :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => (Real.exp_pos _).le)
  have hroot : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  exact mul_nonneg (by positivity) hint

/-- The correction lies in `[0,1]`; the upper inequality is exactly the
Gaussian Mills-ratio estimate. -/
theorem gaussianErfcCorrection_bounds (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ gaussianErfcCorrection t ∧ gaussianErfcCorrection t ≤ 1 := by
  constructor
  · unfold gaussianErfcCorrection
    exact mul_nonneg (by positivity) (gaussianErfc_nonneg t)
  · by_cases hzero : t = 0
    · simp [gaussianErfcCorrection, hzero]
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    have hroot : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
    have hm := mul_le_mul_of_nonneg_left (gaussianErfc_upper t htpos)
      (by positivity : 0 ≤ Real.sqrt Real.pi*t*Real.exp (t^2))
    unfold gaussianErfcCorrection
    calc
      _ ≤ Real.sqrt Real.pi*t*Real.exp (t^2) *
            (Real.exp (-t^2)/(Real.sqrt Real.pi*t)) := hm
      _ = 1 := by
        have hexp : Real.exp (t^2)*Real.exp (-t^2) = 1 := by
          rw [← Real.exp_add]
          simp
        field_simp [hroot.ne', htpos.ne']
        nlinarith [hexp]

#print axioms gaussianErfc_nonneg
#print axioms gaussianErfcCorrection_bounds
end SpectralRadiusUpperTail
