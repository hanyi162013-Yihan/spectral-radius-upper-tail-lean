import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- The shifted exponential envelope is integrable on the right half-line. -/
theorem exponential_right_tail_envelope_integrableOn (A a r : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => A * Real.exp (-a*(x-r))) (Ioi r) := by
  have hbase : IntegrableOn (fun x : ℝ => Real.exp (-a*x)) (Ioi r) :=
    integrableOn_exp_mul_Ioi (show -a < 0 by linarith) r
  have heq : (fun x : ℝ => A * Real.exp (-a*(x-r))) =
      (fun x : ℝ => (A*Real.exp (a*r))*Real.exp (-a*x)) := by
    funext x
    calc
      A * Real.exp (-a*(x-r)) = A * Real.exp (a*r + -a*x) := by
        congr 1
        ring
      _ = (A*Real.exp (a*r))*Real.exp (-a*x) := by
        rw [Real.exp_add]
        ring
  rw [heq]
  exact hbase.const_mul _

/-- The exact mass of the exponential envelope based at a right-tail
threshold. -/
theorem exponential_right_tail_envelope_integral (A a r : ℝ) (ha : 0 < a) :
    (∫ x : ℝ in Ioi r, A * Real.exp (-a*(x-r))) = A/a := by
  have hex (x : ℝ) :
      Real.exp (-a*(x-r)) = Real.exp (a*r) * Real.exp (-a*x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hex]
  rw [integral_const_mul, integral_const_mul,
    integral_exp_mul_Ioi (show -a < 0 by linarith)]
  rw [neg_div_neg_eq]
  have hcancel : Real.exp (a*r) * Real.exp (-a*r) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    A * (Real.exp (a*r) * (Real.exp (-a*r) / a)) =
        A * ((Real.exp (a*r) * Real.exp (-a*r)) / a) := by ring
    _ = A/a := by
      rw [hcancel]
      ring

#print axioms exponential_right_tail_envelope_integral
#print axioms exponential_right_tail_envelope_integrableOn
end SpectralRadiusUpperTail
