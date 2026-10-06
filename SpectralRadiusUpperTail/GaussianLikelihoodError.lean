import SpectralRadiusUpperTail.GaussianLogRatio
import SpectralRadiusUpperTail.SquareExpEnvelope

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma shift_increment_envelope (C v r b q d u : ℝ)
    (hC : 0 ≤ C) (hv : 0 ≤ v) (hr : 0 ≤ r) (hb : 0 ≤ b)
    (hq : 0 ≤ q) (hqr : q ≤ v*r)
    (hsmall : C*v*(1+b+v) ≤ d*u) :
    C*q*(1+b+q) ≤ u*(d*(r+r^2)) := by
  have h1 : C*q*(1+b+q) ≤ C*(v*r)*(1+b+v*r) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hqr hC) (by linarith)
      (by positivity) (by positivity)
  have h2 : C*(v*r)*(1+b+v*r) ≤ C*v*(1+b+v)*(r+r^2) := by
    have hn : 0 ≤ C*v*(v*r+(1+b)*r^2) := by positivity
    nlinarith only [hn]
  have h3 := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ r+r^2 by positivity)
  calc
    _ ≤ C*(v*r)*(1+b+v*r) := h1
    _ ≤ C*v*(1+b+v)*(r+r^2) := h2
    _ ≤ (d*u)*(r+r^2) := h3
    _ = _ := by ring

/-- The actual unnormalized Gaussian likelihood ratio has a small weighted
variation. The future-law exponential moment and entry-law square-exponential
moment are separate hypotheses, so no uniform future-sum estimate is hidden. -/
theorem gaussian_likelihood_weighted_error
    (ν μ : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 ν) (hm : (∫ x : E, x ∂ν) = 0)
    (hvar : (∫ x : E, ‖x‖^2 ∂ν) ≤ 1) (a c L : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hLn : 0 ≤ L)
    (hexp : Integrable (fun x : E => Real.exp (c*‖x‖^2)) ν)
    (hL : (∫ x : E, Real.exp (c*‖x‖^2) ∂ν) ≤ Real.exp L)
    (d : ℝ) (hd : 0 < d)
    (hentry : Integrable (fun x : E => Real.exp (4*d*‖x‖^2)) μ)
    (s : E) (T : E →L[ℝ] E) (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hsmall : gaussianScoreConstant a c L*‖T‖*(1+‖s‖+‖T‖) ≤ d*u) :
    let g := fun x => gaussianConvolution ν a (s-T x)/gaussianConvolution ν a s
    Measurable g ∧ Integrable g μ ∧
      Integrable (fun x => (1+‖x‖^2)*|g x-1|) μ ∧
      (∫ x, (1+‖x‖^2)*|g x-1| ∂μ) ≤
        u * ∫ x, (1+‖x‖^2)*(d*(‖x‖+‖x‖^2))*
          Real.exp (d*(‖x‖+‖x‖^2)) ∂μ := by
  let D := fun x => Real.log (gaussianConvolution ν a (s-T x))-
    Real.log (gaussianConvolution ν a s)
  obtain ⟨hC, hscore⟩ := gaussian_log_score_growth ν hX hm hvar a c L ha hc hLn hexp hL
  have hcont : Continuous (fun t => Real.log (gaussianConvolution ν a t)) :=
    continuous_iff_continuousAt.mpr (fun t => (hscore t).1.continuousAt)
  have hD : Measurable D :=
    ((hcont.comp (continuous_const.sub T.continuous)).sub continuous_const).measurable
  have heq : (fun x => Real.exp (D x)) =
      (fun x => gaussianConvolution ν a (s-T x)/gaussianConvolution ν a s) := by
    funext x
    dsimp [D]
    rw [Real.exp_sub,
      Real.exp_log (gaussianSoftTilt_basics ν hX hm a ha (s-T x)).1,
      Real.exp_log (gaussianSoftTilt_basics ν hX hm a ha s).1]
  have hlog (x : E) : |D x| ≤ u*(d*(‖x‖+‖x‖^2)) := by
    apply (gaussian_log_increment ν hX hm hvar a c L ha hc hLn hexp hL s (T x)).trans
    exact shift_increment_envelope _ _ _ _ _ _ _ hC (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _) (T.le_opNorm x) hsmall
  have hf : Measurable (fun x : E => 1+‖x‖^2) :=
    measurable_const.add (measurable_norm.pow_const 2)
  have hr := exponential_weighted_error μ D (fun x => d*(‖x‖+‖x‖^2))
    (fun x => 1+‖x‖^2) hD hf (fun x => by positivity)
    (fun x => le_add_of_nonneg_right (sq_nonneg _))
    (squareExp_weighted_envelope_integrable μ d hd hentry) u hu hu1 hlog
  have hmeas : Measurable (fun x => Real.exp (D x)) := Real.measurable_exp.comp hD
  rw [heq] at hmeas
  have heq' (x : E) := congrFun heq x
  simp_rw [heq'] at hr
  exact ⟨hmeas, hr⟩

#print axioms gaussian_likelihood_weighted_error
end SpectralRadiusUpperTail
