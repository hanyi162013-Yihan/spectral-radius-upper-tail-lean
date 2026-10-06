import SpectralRadiusUpperTail.PiNormalizedTilt
import SpectralRadiusUpperTail.GaussianMoments
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

lemma standardNormal_eq_normalizedTilt :
    standardNormal = normalizedTilt volume (fun x : ℝ => ENNReal.ofReal (Real.exp (-(1/2)*x^2))) := by
  symm
  have hi := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
  rw [normalizedTilt_ofReal_eq_density volume _ hi (fun x => (Real.exp_pos _).le) (integral_exp_pos hi),
    standardNormal,gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  congr 1
  funext x
  rw [integral_gaussian]
  simp only [gaussianPDF,gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
  have he : -(1/2 : ℝ)*x^2 = -x^2/2 := by ring
  have hp : Real.pi/(1/2 : ℝ) = 2*Real.pi := by ring
  rw [he,hp]
  congr 1
  ring

lemma standardNormal_pi_eq_normalizedTilt (n : ℕ) :
    Measure.pi (fun _ : Fin n => standardNormal) =
      normalizedTilt (Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))
        (fun x : Fin n → ℝ => ENNReal.ofReal (Real.exp (-(∑ i, (x i)^2)/2))) := by
  have he (x : Fin n → ℝ) : Real.exp (-(∑ i, (x i)^2)/2) =
      ∏ i, Real.exp (-(1/2)*(x i)^2) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    ring
  simp_rw [he]
  rw [pi_normalizedTilt_ofReal _ (fun (_ : Fin n) (x : ℝ) => Real.exp (-(1/2)*x^2))
    (fun _ => integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2))
    (fun _ _ => (Real.exp_pos _).le)
    (fun _ => integral_exp_pos (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)))]
  simp only [← standardNormal_eq_normalizedTilt]

#print axioms standardNormal_eq_normalizedTilt
#print axioms standardNormal_pi_eq_normalizedTilt
end SpectralRadiusUpperTail
