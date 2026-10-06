import SpectralRadiusUpperTail.ExponentialRightTailEnvelope
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- A pointwise exponential envelope gives the corresponding integral
upper bound on a half-line. -/
theorem right_tail_integral_le_of_exp_envelope (f : ℝ → ℝ)
    (r A a : ℝ) (ha : 0 < a)
    (hf : IntegrableOn f (Ioi r))
    (hbound : ∀ x, r < x → f x ≤ A * Real.exp (-a*(x-r))) :
    (∫ x : ℝ in Ioi r, f x) ≤ A/a := by
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
  have henv : IntegrableOn (fun x : ℝ => A*Real.exp (-a*(x-r))) (Ioi r) := by
    rw [heq]
    exact hbase.const_mul _
  calc
    (∫ x : ℝ in Ioi r, f x) ≤
        ∫ x : ℝ in Ioi r, A*Real.exp (-a*(x-r)) :=
      setIntegral_mono_on hf henv measurableSet_Ioi (fun x hx => hbound x hx)
    _ = A/a := exponential_right_tail_envelope_integral A a r ha

#print axioms right_tail_integral_le_of_exp_envelope
end SpectralRadiusUpperTail
