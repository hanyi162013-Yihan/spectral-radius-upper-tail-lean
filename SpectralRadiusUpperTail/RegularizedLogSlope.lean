import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

noncomputable def regularizedLogSlope (τ x : ℝ) : ℝ := 2*x/(x^2+τ^2)

lemma regularizedLogSlope_nonneg (τ x : ℝ) (hx : 0 ≤ x) :
    0 ≤ regularizedLogSlope τ x := by unfold regularizedLogSlope; positivity

lemma regularizedLogSlope_le (τ x : ℝ) (hτ : 0 < τ) :
    regularizedLogSlope τ x ≤ 1/τ := by
  have hd : 0 < x^2+τ^2 := by positivity
  rw [regularizedLogSlope, div_le_div_iff₀ hd hτ]
  nlinarith [sq_nonneg (x-τ)]

lemma regularizedLogSlope_monotone (τ : ℝ) (hτ : 0 < τ) :
    MonotoneOn (regularizedLogSlope τ) (Set.Icc 0 τ) := by
  intro x hx y hy hxy
  have hd x : 0 < x^2+τ^2 := by positivity
  rw [regularizedLogSlope, regularizedLogSlope, div_le_div_iff₀ (hd x) (hd y)]
  have hp : x*y ≤ τ*τ := mul_le_mul hx.2 hy.2 hy.1 hτ.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hp)]

lemma regularizedLogSlope_antitone (τ : ℝ) (hτ : 0 < τ) :
    AntitoneOn (regularizedLogSlope τ) (Set.Ici τ) := by
  intro x hx y hy hxy
  have hd x : 0 < x^2+τ^2 := by positivity
  rw [regularizedLogSlope, regularizedLogSlope, div_le_div_iff₀ (hd y) (hd x)]
  have hp : τ*τ ≤ x*y := mul_le_mul hx hy hτ.le (hτ.le.trans hx)
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hp)]

lemma regularizedLogSlope_at_cutoff (τ : ℝ) (hτ : 0 < τ) :
    regularizedLogSlope τ τ = 1/τ := by
  unfold regularizedLogSlope
  field_simp
  <;> ring

lemma regularizedLogSlope_continuous (τ : ℝ) (hτ : 0 < τ) :
    Continuous (regularizedLogSlope τ) := by
  unfold regularizedLogSlope
  exact (continuous_const.mul continuous_id).div
    ((continuous_id.pow 2).add continuous_const) (fun x => ne_of_gt (by positivity))

#print axioms regularizedLogSlope_nonneg
#print axioms regularizedLogSlope_le
#print axioms regularizedLogSlope_monotone
#print axioms regularizedLogSlope_antitone
#print axioms regularizedLogSlope_at_cutoff
#print axioms regularizedLogSlope_continuous
end SpectralRadiusUpperTail
