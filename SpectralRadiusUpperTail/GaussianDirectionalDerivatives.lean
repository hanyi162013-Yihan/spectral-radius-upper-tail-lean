import SpectralRadiusUpperTail.GaussianLineDerivatives

namespace SpectralRadiusUpperTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def gaussianDirectional (a : ℝ) (w z : E) : ℝ :=
  (-2/a)*inner ℝ z w*Real.exp (-‖z‖^2/a)

noncomputable def gaussianDirectionalLineFirst (a : ℝ) (w s h : E) (t : ℝ) : ℝ :=
  (-2/a)*(inner ℝ h w*gaussianLine a s h t+
    inner ℝ (s+t • h) w*gaussianLineFirst a s h t)

noncomputable def gaussianDirectionalLineSecond (a : ℝ) (w s h : E) (t : ℝ) : ℝ :=
  (-2/a)*(2*inner ℝ h w*gaussianLineFirst a s h t+
    inner ℝ (s+t • h) w*gaussianLineSecond a s h t)

noncomputable def gaussianDirectionalLineThird (a : ℝ) (w s h : E) (t : ℝ) : ℝ :=
  (-2/a)*(3*inner ℝ h w*gaussianLineSecond a s h t+
    inner ℝ (s+t • h) w*gaussianLineThird a s h t)

lemma inner_line_deriv (w s h : E) (t : ℝ) :
    HasDerivAt (fun u : ℝ => inner ℝ (s+u • h) w) (inner ℝ h w) t := by
  have hl : HasDerivAt (fun u : ℝ => s+u • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add s
  convert! hl.inner ℝ (hasDerivAt_const t w) using 1 <;> simp

lemma gaussianDirectional_line_deriv (a : ℝ) (w s h : E) (t : ℝ) :
    HasDerivAt (fun u => gaussianDirectional a w (s+u • h))
      (gaussianDirectionalLineFirst a w s h t) t := by
  have hh := ((inner_line_deriv w s h t).mul (gaussianLine_deriv a s h t)).const_mul (-2/a)
  convert! hh using 1 <;>
    (try dsimp [gaussianDirectional, gaussianDirectionalLineFirst, gaussianLine]) <;> ring

lemma gaussianDirectional_first_deriv (a : ℝ) (w s h : E) (t : ℝ) :
    HasDerivAt (gaussianDirectionalLineFirst a w s h)
      (gaussianDirectionalLineSecond a w s h t) t := by
  have hh := (((gaussianLine_deriv a s h t).const_mul (inner ℝ h w)).add
    ((inner_line_deriv w s h t).mul (gaussianLine_first_deriv a s h t))).const_mul (-2/a)
  convert! hh using 1 <;>
    (try dsimp [gaussianDirectionalLineFirst, gaussianDirectionalLineSecond]) <;> ring

lemma gaussianDirectional_second_deriv (a : ℝ) (w s h : E) (t : ℝ) :
    HasDerivAt (gaussianDirectionalLineSecond a w s h)
      (gaussianDirectionalLineThird a w s h t) t := by
  have hh := (((gaussianLine_first_deriv a s h t).const_mul (2*inner ℝ h w)).add
    ((inner_line_deriv w s h t).mul (gaussianLine_second_deriv a s h t))).const_mul (-2/a)
  convert! hh using 1 <;>
    (try dsimp [gaussianDirectionalLineSecond, gaussianDirectionalLineThird]) <;> ring

#print axioms gaussianDirectional_line_deriv
#print axioms gaussianDirectional_second_deriv
end SpectralRadiusUpperTail
