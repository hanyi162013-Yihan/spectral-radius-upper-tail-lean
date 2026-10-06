import SpectralRadiusUpperTail.UniformFutureCoupling
import SpectralRadiusUpperTail.LogDensitySquareExp

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The actual normalized one-entry future kernel has a uniform conditional
square-exponential moment in the local perturbation regime. -/
theorem gaussianFuture_conditional_squareExp (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1) (a d : ℝ)
    (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (s : 𝕂) (T : 𝕂 →L[ℝ] 𝕂) (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hsmall : gaussianScoreConstant a
      (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)) (Real.log 2)*
        ‖T‖*(1+‖s‖+‖T‖) ≤ d*u)
    (herror : u*(∫ x : 𝕂, (1+‖x‖^2)*(d*(‖x‖+‖x‖^2))*
      Real.exp (d*(‖x‖+‖x‖^2)) ∂μ) ≤ 1/2) :
    let W := futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N
    let g := fun x => (W (s-T x)).toReal/(W s).toReal
    let Z := ∫ x, g x ∂μ
    let ν := μ.withDensity (fun x => ENNReal.ofReal (g x/Z))
    IsProbabilityMeasure ν ∧
      Integrable (fun x : 𝕂 => Real.exp (d*‖x‖^2)) ν ∧
      (∫ x : 𝕂, Real.exp (d*‖x‖^2) ∂ν) ≤
        2*Real.exp d*(∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ) := by
  let W := futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N
  let D := fun x => Real.log (W (s-T x)).toReal-Real.log (W s).toReal
  have hf (i : ℕ) : Measurable (fun x : 𝕂 => v i*x) :=
    (continuous_const.mul continuous_id).measurable
  have hW : Measurable W := futureWeight_measurable μ _ _ hf (gaussianSoftWeight_measurable a) N
  have hWp (t : 𝕂) : 0 < (W t).toReal := ENNReal.toReal_pos
    (ne_of_gt (futureWeight_pos μ _ _ hf (gaussianSoftWeight_measurable a)
      (gaussianSoftWeight_pos a) N t))
    (ne_top_of_le_ne_top ENNReal.one_ne_top
      (futureWeight_le_one μ _ _ (gaussianSoftWeight_le_one a ha) N t))
  have hD : Measurable D :=
    ((Real.measurable_log.comp hW.ennreal_toReal).comp
      (measurable_const.sub T.continuous.measurable)).sub measurable_const
  have heq (x : 𝕂) : Real.exp (D x) = (W (s-T x)).toReal/(W s).toReal := by
    dsimp [D]
    rw [Real.exp_sub, Real.exp_log (hWp (s-T x)), Real.exp_log (hWp s)]
  have hC : 0 ≤ gaussianScoreConstant a
      (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)) (Real.log 2) := by
    dsimp [gaussianScoreConstant]
    positivity
  have hlog (x : 𝕂) : |D x| ≤ d*(‖x‖+‖x‖^2) := by
    have hinc := gaussianFutureWeight_log_increment_uniform μ v N hX hm hvar hv a (4*d)
      ha (by positivity) hexp s (T x)
    apply hinc.trans
    apply (shift_increment_envelope _ _ _ _ _ _ _ hC (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _) (T.le_opNorm x) hsmall).trans
    exact mul_le_of_le_one_left (by positivity) hu1
  have hcouple := gaussianFuture_likelihood_coupling μ v N hX hm hvar hv a d ha hd
    hexp s T u hu hu1 hsmall herror
  have hZhalf : 1/2 ≤ ∫ x, Real.exp (D x) ∂μ := by
    simp_rw [heq]
    exact hcouple.1
  have hh := log_density_squareExp μ D hD d hd hlog hexp hZhalf
  dsimp only at hh ⊢
  simp_rw [heq] at hh
  exact hh

#print axioms gaussianFuture_conditional_squareExp
end SpectralRadiusUpperTail
