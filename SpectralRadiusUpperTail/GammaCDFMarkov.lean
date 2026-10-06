import SpectralRadiusUpperTail.GammaUnitFirstMoment
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A one-line Markov bound keeps a polynomial fraction of the Gamma mass
below any threshold larger than the shape. -/
theorem gamma_unit_cdf_markov_lower (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    (1 : ℝ≥0∞) - ENNReal.ofReal a / ENNReal.ofReal b ≤
      gammaMeasure a 1 (Set.Iic b) := by
  haveI : IsProbabilityMeasure (gammaMeasure a 1) :=
    isProbabilityMeasure_gammaMeasure ha (by norm_num : (0 : ℝ) < 1)
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal x) := by fun_prop
  have hmark := mul_meas_ge_le_lintegral
    (μ := gammaMeasure a 1) hm (ENNReal.ofReal b)
  rw [gamma_unit_firstMoment_lintegral a ha] at hmark
  have hsub : Set.Ioi b ⊆ {x : ℝ | ENNReal.ofReal b ≤ ENNReal.ofReal x} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal hx.le
  have htail : gammaMeasure a 1 (Set.Ioi b) ≤
      ENNReal.ofReal a / ENNReal.ofReal b := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hb))
      (Or.inl (by simp))).2
    rw [mul_comm]
    calc
      ENNReal.ofReal b * gammaMeasure a 1 (Set.Ioi b) ≤
          ENNReal.ofReal b * gammaMeasure a 1
            {x : ℝ | ENNReal.ofReal b ≤ ENNReal.ofReal x} := by
        gcongr
      _ ≤ ENNReal.ofReal a := hmark
  have hcomp := tsub_le_tsub_left htail (1 : ℝ≥0∞)
  simpa only [← prob_compl_eq_one_sub measurableSet_Ioi, Set.compl_Ioi] using hcomp

#print axioms gamma_unit_cdf_markov_lower
end SpectralRadiusUpperTail
