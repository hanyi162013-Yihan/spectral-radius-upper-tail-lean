import SpectralRadiusUpperTail.Rate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace SpectralRadiusUpperTail

noncomputable def annealedTiltRate (β b u : ℝ) : ℝ :=
  β/2*(Real.log (u/(1+u))-b^2/(1+u))

noncomputable def lowerTiltCost (β b u ell κ δ : ℝ) : ℝ :=
  β/2*(b^2/(1+u)+Real.log (1+u)-2*Real.log b-1+ell)+κ+δ

lemma spherical_minus_annealed_cost (β b u ell κ δ : ℝ) (hu : 0 < u) :
    (β/2*Real.log u+β/2*(ell-1)-β*Real.log b+κ+δ)-annealedTiltRate β b u =
      lowerTiltCost β b u ell κ δ := by
  unfold annealedTiltRate lowerTiltCost
  rw [Real.log_div (ne_of_gt hu) (by positivity : (1+u : ℝ) ≠ 0)]
  ring

lemma lowerTiltCost_zero (β b : ℝ) : lowerTiltCost β b 0 0 0 0 = rate β b := by
  simp only [lowerTiltCost,rate,add_zero,div_one,Real.log_one]
  ring

lemma lowerTiltCost_continuousAt_zero (β b : ℝ) :
    ContinuousAt (fun s : ℝ => lowerTiltCost β b s s s s) 0 := by
  unfold lowerTiltCost
  fun_prop (disch := norm_num)

#print axioms annealedTiltRate
#print axioms lowerTiltCost
#print axioms spherical_minus_annealed_cost
#print axioms lowerTiltCost_zero
#print axioms lowerTiltCost_continuousAt_zero
end SpectralRadiusUpperTail
