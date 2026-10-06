import SpectralRadiusUpperTail.GaussianDifferentiation
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def gaussianLine (a : ℝ) (s h : E) (t : ℝ) : ℝ :=
  Real.exp (-‖s+t • h‖^2/a)

noncomputable def gaussianLineSlope (a : ℝ) (s h : E) (t : ℝ) : ℝ :=
  (-2/a)*inner ℝ (s+t • h) h

noncomputable def gaussianLineFirst (a : ℝ) (s h : E) (t : ℝ) : ℝ :=
  gaussianLineSlope a s h t*gaussianLine a s h t

noncomputable def gaussianLineSecond (a : ℝ) (s h : E) (t : ℝ) : ℝ :=
  ((-2/a)*‖h‖^2+(gaussianLineSlope a s h t)^2)*gaussianLine a s h t

noncomputable def gaussianLineThird (a : ℝ) (s h : E) (t : ℝ) : ℝ :=
  (3*((-2/a)*‖h‖^2)*gaussianLineSlope a s h t+
    (gaussianLineSlope a s h t)^3)*gaussianLine a s h t

lemma gaussianLine_slope_deriv (a : ℝ) (s h : E) (t : ℝ) :
    HasDerivAt (gaussianLineSlope a s h) ((-2/a)*‖h‖^2) t := by
  have hline : HasDerivAt (fun u : ℝ => s+u • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add s
  have hh := (hline.inner ℝ (hasDerivAt_const t h)).const_mul (-2/a)
  convert! hh using 1 <;> simp [gaussianLineSlope, real_inner_self_eq_norm_sq]

lemma gaussianLine_deriv (a : ℝ) (s h : E) (t : ℝ) :
    HasDerivAt (gaussianLine a s h) (gaussianLineFirst a s h t) t := by
  have hline : HasDerivAt (fun u : ℝ => s+u • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add s
  have hh := ((hline.norm_sq.neg).div_const a).exp
  convert! hh using 1 <;> (try dsimp [gaussianLine, gaussianLineFirst, gaussianLineSlope]) <;> ring

lemma gaussianLine_first_deriv (a : ℝ) (s h : E) (t : ℝ) :
    HasDerivAt (gaussianLineFirst a s h) (gaussianLineSecond a s h t) t := by
  have hh := (gaussianLine_slope_deriv a s h t).mul (gaussianLine_deriv a s h t)
  convert! hh using 1 <;> (try dsimp [gaussianLineFirst, gaussianLineSecond]) <;> ring

lemma gaussianLine_second_deriv (a : ℝ) (s h : E) (t : ℝ) :
    HasDerivAt (gaussianLineSecond a s h) (gaussianLineThird a s h t) t := by
  have hp := (hasDerivAt_const t ((-2/a)*‖h‖^2)).add
    ((gaussianLine_slope_deriv a s h t).pow 2)
  have hh := hp.mul (gaussianLine_deriv a s h t)
  convert! hh using 1 <;> (try dsimp [gaussianLineFirst, gaussianLineSecond, gaussianLineThird]) <;> ring

#print axioms gaussianLine_slope_deriv
#print axioms gaussianLine_deriv
#print axioms gaussianLine_first_deriv
#print axioms gaussianLine_second_deriv
end SpectralRadiusUpperTail
