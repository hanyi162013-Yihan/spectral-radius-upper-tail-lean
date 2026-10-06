import SpectralRadiusUpperTail.ExponentialFirstMoment

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

lemma exponential_tail_real (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) :
    (expMeasure r).real (Ioi t) = Real.exp (-(r*t)) := by
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ,
    ← cdf_eq_real, cdf_expMeasure_eq hr t, if_pos ht]
  ring

lemma exponential_tail (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) :
    expMeasure r (Ioi t) = ENNReal.ofReal (Real.exp (-(r*t))) := by
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  calc
    expMeasure r (Ioi t) = ENNReal.ofReal ((expMeasure r).real (Ioi t)) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = _ := congrArg ENNReal.ofReal (exponential_tail_real r t hr ht)

#print axioms exponential_tail_real
#print axioms exponential_tail
end SpectralRadiusUpperTail
