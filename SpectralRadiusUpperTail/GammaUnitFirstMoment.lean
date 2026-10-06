import SpectralRadiusUpperTail.ExponentialFirstMoment
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Multiplication by the coordinate raises the shape of a unit-rate
Gamma density by one. -/
lemma gamma_unit_firstMoment_density (a : ℝ) (ha : 0 < a) (x : ℝ) :
    gammaPDF a 1 x * ENNReal.ofReal x =
      ENNReal.ofReal a * gammaPDF (a+1) 1 x := by
  by_cases hx : 0 ≤ x
  · by_cases hx0 : x = 0
    · subst x
      simp [gammaPDF, gammaPDFReal, Real.zero_rpow ha.ne']
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      rw [gammaPDF_of_nonneg hx, gammaPDF_of_nonneg hx]
      rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have hG : Real.Gamma (a+1) = a*Real.Gamma a :=
        Real.Gamma_add_one ha.ne'
      have hpow : x^(a-1)*x = x^a := by
        have h := Real.rpow_add hxpos (a-1) 1
        simpa only [Real.rpow_one, show a-1+1=a by ring] using h.symm
      simp only [Real.one_rpow, one_mul, add_sub_cancel_right]
      rw [hG]
      have hapos : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
      field_simp [ha.ne', hapos.ne']
      nlinarith [hpow]
  · have hxneg : x < 0 := lt_of_not_ge hx
    rw [gammaPDF_of_neg hxneg, gammaPDF_of_neg hxneg]
    simp

/-- The unit-rate Gamma distribution has mean equal to its shape. -/
lemma gamma_unit_firstMoment_lintegral (a : ℝ) (ha : 0 < a) :
    (∫⁻ x : ℝ, ENNReal.ofReal x ∂gammaMeasure a 1) = ENNReal.ofReal a := by
  have hd : Measurable (gammaPDF a 1) :=
    (measurable_gammaPDFReal a 1).ennreal_ofReal
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul volume hd (by fun_prop)]
  simp only [Pi.mul_apply]
  simp_rw [gamma_unit_firstMoment_density a ha]
  have hg : Measurable (gammaPDF (a+1) 1) :=
    (measurable_gammaPDFReal (a+1) 1).ennreal_ofReal
  rw [lintegral_const_mul _ hg,
    lintegral_gammaPDF_eq_one (by linarith : 0 < a+1) (by norm_num : (0 : ℝ) < 1),
    mul_one]

#print axioms gamma_unit_firstMoment_density
#print axioms gamma_unit_firstMoment_lintegral
end SpectralRadiusUpperTail
