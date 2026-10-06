import SpectralRadiusUpperTail.GaussianRowRegression
import SpectralRadiusUpperTail.GaussianRowPrefixTail

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- The actual measurable regression residual is square integrable under the
actual tilted row law, and its noncompact part has an explicit Gaussian tail. -/
theorem gaussianRowRegression_square_integrable_tail (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (v : ℕ → 𝕂) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (a : ℝ) (ha : 0 < a) (j : Fin N) (t : 𝕂) (K : ℝ) (ht : ‖t‖ ≤ K)
    (hsmall : gaussianGlobalScoreConstant μ a d*‖v j.val‖^2 ≤ d)
    (hγ : (4*((gaussianGlobalScoreConstant μ a d)^2/(4*d)+1))*‖v j.val‖^2 ≤
      (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ))/8)
    (η : ℝ) (hη : 0 < η) (R : ℝ) (hR : 0 ≤ R) :
    let c := rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)
    let P := 4*((gaussianGlobalMeanConstant μ a d)^2+1/η^2)
    let γ := (4*((gaussianGlobalScoreConstant μ a d)^2/(4*d)+1))*‖v j.val‖^2
    let ν := gaussianFiniteRowLaw μ a (fun i : Fin N => v i.val) t
    Integrable (fun x => ‖gaussianRowRegression μ a v j t η x‖^2) ν ∧
      (∫ x in {x | R < ‖upperRowTarget v j t x‖}, ‖gaussianRowRegression μ a v j t η x‖^2 ∂ν) ≤
        (P*‖v j.val‖^2)*((Real.exp γ*(1+8/c))*Real.exp (-(c/4)*R^2)*
          (2*Real.exp ((K^2+1)/a+c*K^2))) := by
  let c := rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)
  let P := 4*((gaussianGlobalMeanConstant μ a d)^2+1/η^2)
  let γ := (4*((gaussianGlobalScoreConstant μ a d)^2/(4*d)+1))*‖v j.val‖^2
  let ν := gaussianFiniteRowLaw μ a (fun i : Fin N => v i.val) t
  let W := fun x : Fin N → 𝕂 =>
    (1+‖upperRowTarget v j t x‖^2)*Real.exp (γ*(1+‖upperRowTarget v j t x‖^2))
  have hX : MemLp (fun x : 𝕂 => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 2)
  have hmR := (gaussianRowRegression_continuous μ hX hm hvar a ha v hv j t η).norm.pow 2
  have hP : 0 ≤ P*‖v j.val‖^2 := by dsimp [P]; positivity
  have hbound (x : Fin N → 𝕂) :
      ‖gaussianRowRegression μ a v j t η x‖^2 ≤ (P*‖v j.val‖^2)*W x := by
    have hh := gaussianRowRegression_global_square μ hm hvar d hd hexp v hv a ha j t hsmall η hη x
    simpa only [W, P, γ, mul_assoc] using hh
  have htail := gaussianFiniteRowLaw_regression_weight_tail μ hm hvar (4*d) (by positivity) hexp
    (fun i : Fin N => v i.val) (upperRowCoefficients v j) hv (upperRowCoefficients_energy v j hv)
    a ha t K ht γ R hR hγ
  have hWi : Integrable W ν := htail.1
  have hi : Integrable (fun x => ‖gaussianRowRegression μ a v j t η x‖^2) ν :=
    (hWi.const_mul (P*‖v j.val‖^2)).mono_nonneg hmR.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (Filter.Eventually.of_forall hbound)
  refine ⟨hi, ?_⟩
  have hh := integral_mono (μ := ν.restrict {x | R < ‖upperRowTarget v j t x‖}) hi.integrableOn
    (hWi.const_mul (P*‖v j.val‖^2)).integrableOn hbound
  rw [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left htail.2 hP)

#print axioms gaussianRowRegression_square_integrable_tail
end SpectralRadiusUpperTail
