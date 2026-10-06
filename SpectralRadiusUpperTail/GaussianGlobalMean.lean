import SpectralRadiusUpperTail.GlobalTiltMean
import SpectralRadiusUpperTail.GaussianEntryFutureBridge
import SpectralRadiusUpperTail.UniformFutureScore

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

noncomputable def gaussianGlobalScoreConstant (μ : Measure 𝕂) (a d : ℝ) : ℝ :=
  gaussianScoreConstant a
    (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)) (Real.log 2)

noncomputable def gaussianGlobalMeanConstant (μ : Measure 𝕂) (a d : ℝ) : ℝ :=
  let C := gaussianGlobalScoreConstant μ a d
  C*(∫ x : 𝕂, (‖x‖^2+‖x‖^3)*Real.exp (2*d*‖x‖^2) ∂μ)*Real.exp (9*C^2)

/-- The actual entry kernel has a global mean bound. The current coefficient
must be small, but no compactness restriction is imposed on the target s. -/
theorem gaussianEntry_mean_global (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (v : ℕ → 𝕂) (N : ℕ) (a : ℝ) (ha : 0 < a) (b s : 𝕂)
    (hv : ‖b‖^2+∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (hsmall : gaussianGlobalScoreConstant μ a d*‖b‖^2 ≤ d) :
    ‖∫ x : 𝕂, x ∂gaussianEntryLaw μ a (fun i : Fin N => v i.val) b s‖ ≤
      gaussianGlobalMeanConstant μ a d*(‖b‖*(1+‖s‖))*
        Real.exp ((gaussianGlobalScoreConstant μ a d^2/(4*d)+1)*(‖b‖*(1+‖s‖))^2) := by
  have hX : MemLp (fun x : 𝕂 => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 2)
  let C := gaussianGlobalScoreConstant μ a d
  let u := ‖b‖*(1+‖s‖)
  let W := futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N
  let D := fun x : 𝕂 => Real.log (W (s-b*x)).toReal-Real.log (W s).toReal
  have hC : 0 ≤ C := by dsimp [C, gaussianGlobalScoreConstant, gaussianScoreConstant]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv' : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1 := by nlinarith [sq_nonneg ‖b‖]
  have hb : ‖b‖ ≤ 1 := by
    have hq : 0 ≤ ∑ i : Fin N, ‖v i.val‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith [norm_nonneg b]
  have heu : ‖b‖^2 ≤ u := by dsimp [u]; nlinarith [norm_nonneg b, norm_nonneg s]
  have hf (i : ℕ) : Measurable (fun x : 𝕂 => v i*x) := by fun_prop
  have hW : Measurable W := futureWeight_measurable μ _ _ hf (gaussianSoftWeight_measurable a) N
  have hWp (t : 𝕂) : 0 < (W t).toReal := ENNReal.toReal_pos
    (ne_of_gt (futureWeight_pos μ _ _ hf (gaussianSoftWeight_measurable a)
      (gaussianSoftWeight_pos a) N t))
    (ne_top_of_le_ne_top ENNReal.one_ne_top
      (futureWeight_le_one μ _ _ (gaussianSoftWeight_le_one a ha) N t))
  have hDm : Measurable D :=
    ((Real.measurable_log.comp hW.ennreal_toReal).comp (by fun_prop)).sub measurable_const
  have heq (x : 𝕂) : Real.exp (D x) = (W (s-b*x)).toReal/(W s).toReal := by
    dsimp [D]
    rw [Real.exp_sub, Real.exp_log (hWp (s-b*x)), Real.exp_log (hWp s)]
  have hlog (x : 𝕂) : |D x| ≤ C*u*‖x‖+C*‖b‖^2*‖x‖^2 := by
    have hh := gaussianFutureWeight_log_increment_uniform μ v N hX hm hvar hv' a (4*d)
      ha (by positivity) hexp s (b*x)
    convert! hh using 1 <;> dsimp [D, W, C, u, gaussianGlobalScoreConstant] <;> rw [norm_mul] <;> ring
  have hh := global_tilt_mean μ D hDm C u (‖b‖^2) d hC hu (sq_nonneg _) heu hd hsmall hlog hm hvar hexp
  dsimp only at hh
  have hlaw := gaussianEntryLaw_eq_future_likelihood μ hX hm hvar v N a ha b s hv
  dsimp only at hlaw
  rw [hlaw]
  dsimp only [W] at heq
  simp_rw [← heq]
  exact hh.2.2

#print axioms gaussianEntry_mean_global
end SpectralRadiusUpperTail
