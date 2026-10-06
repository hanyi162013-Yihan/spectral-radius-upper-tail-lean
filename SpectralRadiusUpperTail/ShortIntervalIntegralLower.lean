import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set intervalIntegral

/-- A pointwise lower bound on a finite interval gives its length times
the lower bound in the integral. -/
theorem short_interval_integral_lower (f : ℝ → ℝ)
    (a b c : ℝ) (hab : a ≤ b)
    (hf : IntegrableOn f (Ioc a b))
    (hbound : ∀ x ∈ Icc a b, c ≤ f x) :
    (b-a)*c ≤ ∫ x : ℝ in Ioc a b, f x := by
  have hif : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hf
  have hic : IntervalIntegrable (fun _ : ℝ => c) volume a b :=
    intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on hab hic hif hbound
  have hc : (∫ x : ℝ in Ioc a b, c) = (b-a)*c := by
    calc
      (∫ x : ℝ in Ioc a b, c) = ∫ x in a..b, c :=
        (intervalIntegral.integral_of_le hab).symm
      _ = (b-a)*c := by simp [smul_eq_mul]
  simp only [intervalIntegral.integral_of_le hab] at h
  rw [hc] at h
  exact h

#print axioms short_interval_integral_lower
end SpectralRadiusUpperTail
