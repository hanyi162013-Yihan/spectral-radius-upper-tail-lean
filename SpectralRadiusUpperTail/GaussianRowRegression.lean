import SpectralRadiusUpperTail.FiniteRevealedRow
import SpectralRadiusUpperTail.GaussianEntryContinuity
import SpectralRadiusUpperTail.GaussianGlobalRegression
import SpectralRadiusUpperTail.ShiftedEntryRegression

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- Actual descending-order regression residual on a complete tilted row.
The denominator includes the current coordinate and all unrevealed coordinates. -/
noncomputable def gaussianRowRegression (μ : Measure 𝕂) (a : ℝ) (v : ℕ → 𝕂)
    (j : Fin N) (t : 𝕂) (η : ℝ) (x : Fin N → 𝕂) : 𝕂 :=
  (∫ z : 𝕂, z ∂gaussianEntryLaw μ a (fun i : Fin j.val => v i.val) (v j.val)
      (upperRowTarget v j t x))-
    (1/(η+(∑ i : Fin j.val, ‖v i.val‖^2)+‖v j.val‖^2) : ℝ) •
      (star (v j.val)*upperRowTarget v j t x)

lemma gaussianRowRegression_continuous (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (a : ℝ) (ha : 0 < a)
    (v : ℕ → 𝕂) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (j : Fin N) (t : 𝕂) (η : ℝ) : Continuous (gaussianRowRegression μ a v j t η) := by
  have hS := upperRowTarget_continuous v j t
  have hmean := (gaussianEntryLaw_mean_continuous_of_energy μ hX hm hvar a ha
    (fun i : Fin j.val => v i.val) (v j.val) (current_future_energy v j hv)).comp hS
  exact hmean.sub (continuous_const.smul (continuous_const.mul hS))

/-- The global bound now applies to the actual measurable full-row residual. -/
theorem gaussianRowRegression_global_square (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (v : ℕ → 𝕂) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (a : ℝ) (ha : 0 < a) (j : Fin N) (t : 𝕂)
    (hsmall : gaussianGlobalScoreConstant μ a d*‖v j.val‖^2 ≤ d)
    (η : ℝ) (hη : 0 < η) (x : Fin N → 𝕂) :
    ‖gaussianRowRegression μ a v j t η x‖^2 ≤
      (4*((gaussianGlobalMeanConstant μ a d)^2+1/η^2))*‖v j.val‖^2*
        (1+‖upperRowTarget v j t x‖^2)*Real.exp
          ((4*((gaussianGlobalScoreConstant μ a d)^2/(4*d)+1))*‖v j.val‖^2*
            (1+‖upperRowTarget v j t x‖^2)) := by
  exact gaussianEntry_regression_global_square μ hm hvar d hd hexp v j.val a ha (v j.val)
    (upperRowTarget v j t x) (current_future_energy v j hv) hsmall η hη

/-- The compact real estimate is for these same actual full-row residuals. -/
theorem real_gaussianRowRegression_compact (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (τ : ℝ) (hτ : 0 < τ) (hexp : Integrable (fun x : ℝ => Real.exp (τ*‖x‖^2)) μ)
    (v : ℕ → ℝ) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (j : Fin N) (t : ℝ) (η : ℝ) (hη : 0 < η) (R : ℝ) (x : Fin N → ℝ)
    (hx : ‖upperRowTarget v j t x‖ ≤ R) :
    ‖gaussianRowRegression μ (2*η) v j t η x‖ ≤
      gaussianEntryTaylorConstant (2*η) R 1 (∫ z : ℝ, ‖z‖^3 ∂μ)*‖v j.val‖^2+
      gaussianScoreComparisonConstant (2*η) R*‖v j.val‖*
        ((∫ z : ℝ, ‖z‖^3 ∂μ)+(∫ z : ℝ, ‖z‖^3 ∂standardNormal))*
          (∑ i : Fin j.val, ‖v i.val‖^3)+
      (‖upperRowTarget v j t x‖/η^2)*‖v j.val‖^3 := by
  exact real_gaussian_entry_regression_full_tail μ hm hvar τ hτ hexp η hη j.val
    (fun i : Fin j.val => v i.val) (v j.val) (upperRowTarget v j t x)
    (current_future_energy v j hv) R hx

/-- Properness is required only for the compact complex matching regression. -/
theorem complex_gaussianRowRegression_compact (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (τ : ℝ) (hτ : 0 < τ) (hexp : Integrable (fun x : ℂ => Real.exp (τ*‖x‖^2)) μ)
    (v : ℕ → ℂ) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (j : Fin N) (t : ℂ) (η : ℝ) (hη : 0 < η) (R : ℝ) (x : Fin N → ℂ)
    (hx : ‖upperRowTarget v j t x‖ ≤ R) :
    ‖gaussianRowRegression μ η v j t η x‖ ≤
      gaussianEntryTaylorConstant η R (1/2) (∫ z : ℂ, ‖z‖^3 ∂μ)*‖v j.val‖^2+
      (1/2)*gaussianScoreComparisonConstant η R*‖v j.val‖*
        ((∫ z : ℂ, ‖z‖^3 ∂μ)+(∫ z : ℂ, ‖z‖^3 ∂properComplexGaussian))*
          (∑ i : Fin j.val, ‖v i.val‖^3)+
      (‖upperRowTarget v j t x‖/η^2)*‖v j.val‖^3 := by
  exact complex_gaussian_entry_regression_full_tail μ hm hvar hpseudo τ hτ hexp η hη j.val
    (fun i : Fin j.val => v i.val) (v j.val) (upperRowTarget v j t x)
    (current_future_energy v j hv) R hx

#print axioms gaussianRowRegression_continuous
#print axioms gaussianRowRegression_global_square
#print axioms complex_gaussianRowRegression_compact
end SpectralRadiusUpperTail
