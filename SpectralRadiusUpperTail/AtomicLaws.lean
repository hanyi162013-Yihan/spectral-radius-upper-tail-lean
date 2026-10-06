import SpectralRadiusUpperTail.FourPoint
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

noncomputable def fourPointMeasure : Measure (ℝ × ℝ) :=
  (1/4 : ℝ≥0∞) • (Measure.dirac (1,0) + Measure.dirac (-1,0) +
    Measure.dirac (0,1) + Measure.dirac (0,-1))

lemma integral_fourPoint (f : ℝ × ℝ → ℝ) :
    (∫ x, f x ∂fourPointMeasure) =
      (f (1,0)+f (-1,0)+f (0,1)+f (0,-1))/4 := by
  have h (a : ℝ × ℝ) : Integrable f (Measure.dirac a) := integrable_dirac (by simp)
  rw [fourPointMeasure, integral_smul_measure]
  simp [integral_add_measure, integrable_add_measure, h, integral_dirac]
  <;> ring

lemma fourPoint_integrable (f : ℝ × ℝ → ℝ) : Integrable f fourPointMeasure := by
  have h (a : ℝ × ℝ) : Integrable f (Measure.dirac a) := integrable_dirac (by simp)
  exact (((h _).add_measure (h _)).add_measure (h _)).add_measure (h _) |>.smul_measure (by norm_num)

theorem fourPoint_laplace (a b : ℝ) :
    (∫ x : ℝ × ℝ, Real.exp (2*(a*x.1+b*x.2)) ∂fourPointMeasure)
      ≤ Real.exp (a^2+b^2) := by
  rw [integral_fourPoint]
  simpa [fourPointMGF, mul_neg] using fourPointMGF_le a b

theorem fourPoint_center_re : (∫ x : ℝ × ℝ, x.1 ∂fourPointMeasure) = 0 := by
  rw [integral_fourPoint]; norm_num

theorem fourPoint_center_im : (∫ x : ℝ × ℝ, x.2 ∂fourPointMeasure) = 0 := by
  rw [integral_fourPoint]; norm_num

theorem fourPoint_variance : (∫ x : ℝ × ℝ, x.1^2+x.2^2 ∂fourPointMeasure) = 1 := by
  rw [integral_fourPoint]; norm_num

theorem fourPoint_pseudovariance_re :
    (∫ x : ℝ × ℝ, x.1^2-x.2^2 ∂fourPointMeasure) = 0 := by
  rw [integral_fourPoint]; norm_num

theorem fourPoint_pseudovariance_im :
    (∫ x : ℝ × ℝ, 2*x.1*x.2 ∂fourPointMeasure) = 0 := by
  rw [integral_fourPoint]; norm_num

#print axioms fourPoint_laplace
#print axioms fourPoint_variance
end SpectralRadiusUpperTail
