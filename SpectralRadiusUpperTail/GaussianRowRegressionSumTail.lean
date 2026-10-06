import SpectralRadiusUpperTail.GaussianRowRegressionTail

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- Summing the actual regression tails costs only the total coefficient
energy. The displayed tail constant is independent of the row length. -/
theorem gaussianRowRegression_sum_tail (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (v : ℕ → 𝕂) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (a : ℝ) (ha : 0 < a) (t : 𝕂) (K : ℝ) (ht : ‖t‖ ≤ K)
    (hsmall : ∀ j : Fin N, gaussianGlobalScoreConstant μ a d*‖v j.val‖^2 ≤ d)
    (hγ : ∀ j : Fin N, (4*((gaussianGlobalScoreConstant μ a d)^2/(4*d)+1))*‖v j.val‖^2 ≤
      (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ))/8)
    (η : ℝ) (hη : 0 < η) (R : ℝ) (hR : 0 ≤ R) :
    let c := rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)
    let P := 4*((gaussianGlobalMeanConstant μ a d)^2+1/η^2)
    let ν := gaussianFiniteRowLaw μ a (fun i : Fin N => v i.val) t
    Integrable (fun x => ∑ j : Fin N, ‖gaussianRowRegression μ a v j t η x‖^2) ν ∧
      (∑ j : Fin N, ∫ x in {x | R < ‖upperRowTarget v j t x‖},
        ‖gaussianRowRegression μ a v j t η x‖^2 ∂ν) ≤
        P*(Real.exp (c/8)*(1+8/c))*Real.exp (-(c/4)*R^2)*
          (2*Real.exp ((K^2+1)/a+c*K^2)) := by
  let c := rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)
  let P := 4*((gaussianGlobalMeanConstant μ a d)^2+1/η^2)
  let ν := gaussianFiniteRowLaw μ a (fun i : Fin N => v i.val) t
  let T := P*(Real.exp (c/8)*(1+8/c))*Real.exp (-(c/4)*R^2)*
    (2*Real.exp ((K^2+1)/a+c*K^2))
  have hc : 0 < c := (gaussianFiniteRowLaw_shifted_sum_squareExp μ hm hvar
    (4*d) (by positivity) hexp (fun i : Fin N => v i.val) (fun i : Fin N => v i.val)
    hv hv a ha t K ht).1
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hj (j : Fin N) := gaussianRowRegression_square_integrable_tail μ hm hvar d hd hexp v hv
    a ha j t K ht (hsmall j) (hγ j) η hη R hR
  refine ⟨integrable_finsetSum _ (fun j _ => (hj j).1), ?_⟩
  have hone (j : Fin N) :
      (∫ x in {x | R < ‖upperRowTarget v j t x‖},
        ‖gaussianRowRegression μ a v j t η x‖^2 ∂ν) ≤ ‖v j.val‖^2*T := by
    apply (hj j).2.trans
    calc
      _ ≤ (P*‖v j.val‖^2)*((Real.exp (c/8)*(1+8/c))*Real.exp (-(c/4)*R^2)*
          (2*Real.exp ((K^2+1)/a+c*K^2))) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hP (sq_nonneg _))
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hγ j)) (by positivity)
      _ = ‖v j.val‖^2*T := by dsimp [T]; ring
  calc
    _ ≤ ∑ j : Fin N, ‖v j.val‖^2*T := Finset.sum_le_sum (fun j _ => hone j)
    _ = (∑ j : Fin N, ‖v j.val‖^2)*T := (Finset.sum_mul _ _ _).symm
    _ ≤ 1*T := mul_le_mul_of_nonneg_right hv hT
    _ = T := one_mul _

#print axioms gaussianRowRegression_sum_tail
end SpectralRadiusUpperTail
