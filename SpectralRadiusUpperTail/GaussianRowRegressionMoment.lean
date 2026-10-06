import SpectralRadiusUpperTail.GaussianRowRegressionSumTail
import SpectralRadiusUpperTail.FlatRegressionCompact
import SpectralRadiusUpperTail.CompactTailIntegration

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

lemma gaussianFiniteRowLaw_probability (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1) (a : ℝ) (ha : 0 < a) (t : 𝕂) :
    IsProbabilityMeasure (gaussianFiniteRowLaw μ a (fun i : Fin N => v i.val) t) := by
  obtain ⟨Γ, hΓ, hfirst, _⟩ := gaussianRow_coupling_exists μ v a ha N t
  letI : IsProbabilityMeasure Γ := hΓ
  rw [gaussianFiniteRowLaw_eq_coupling_source μ hX hm hvar v N hv a ha, ← hfirst]
  exact Measure.isProbabilityMeasure_map
    (measurable_coordinateVector Prod.fst measurable_fst N).aemeasurable

/-- Explicit dimension-independent contribution of all noncompact residuals. -/
noncomputable def gaussianRowRegressionTailBound (μ : Measure 𝕂) (a d η K R : ℝ) : ℝ :=
  let c := rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)
  (4*((gaussianGlobalMeanConstant μ a d)^2+1/η^2))*(Real.exp (c/8)*(1+8/c))*
    Real.exp (-(c/4)*R^2)*(2*Real.exp ((K^2+1)/a+c*K^2))

/-- The actual row's expected squared residual sum follows from its proved
global tail and any verified compact coefficient bound. -/
theorem gaussianRowRegression_integral_le_of_compact (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (v : ℕ → 𝕂) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (a : ℝ) (ha : 0 < a) (t : 𝕂) (K : ℝ) (ht : ‖t‖ ≤ K)
    (hsmall : ∀ j : Fin N, gaussianGlobalScoreConstant μ a d*‖v j.val‖^2 ≤ d)
    (hγ : ∀ j : Fin N, (4*((gaussianGlobalScoreConstant μ a d)^2/(4*d)+1))*‖v j.val‖^2 ≤
      (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ))/8)
    (η : ℝ) (hη : 0 < η) (R : ℝ) (hR : 0 ≤ R) (C δ : ℝ)
    (hcompact : ∀ j : Fin N, ∀ x : Fin N → 𝕂, ‖upperRowTarget v j t x‖ ≤ R →
      ‖gaussianRowRegression μ a v j t η x‖ ≤ C*δ*‖v j.val‖) :
    (∫ x, ∑ j : Fin N, ‖gaussianRowRegression μ a v j t η x‖^2
      ∂gaussianFiniteRowLaw μ a (fun i : Fin N => v i.val) t) ≤
        C^2*δ^2+gaussianRowRegressionTailBound μ a d η K R := by
  have hX : MemLp (fun x : 𝕂 => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 2)
  letI := gaussianFiniteRowLaw_probability μ hX hm hvar v hv a ha t
  apply sum_integral_sq_le_compact_add_tail _ (fun j => gaussianRowRegression μ a v j t η)
    (fun j => upperRowTarget v j t) (fun j => (upperRowTarget_continuous v j t).measurable)
    (fun j => (gaussianRowRegression_square_integrable_tail μ hm hvar d hd hexp v hv
      a ha j t K ht (hsmall j) (hγ j) η hη R hR).1) (fun j => ‖v j.val‖) hv C δ R
    (gaussianRowRegressionTailBound μ a d η K R) hcompact
  exact (gaussianRowRegression_sum_tail μ hm hvar d hd hexp v hv a ha t K ht hsmall hγ η hη R hR).2

/-- Fully instantiated finite expected row error for real entries: compact
flatness error plus a dimension-independent Gaussian tail. -/
theorem real_gaussianRowRegression_secondMoment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℝ => Real.exp (4*d*‖x‖^2)) μ)
    (v : ℕ → ℝ) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (δ : ℝ) (hflat : ∀ j : Fin N, ‖v j.val‖ ≤ δ)
    (η : ℝ) (hη : 0 < η) (t : ℝ) (K : ℝ) (ht : ‖t‖ ≤ K)
    (hsmall : ∀ j : Fin N, gaussianGlobalScoreConstant μ (2*η) d*‖v j.val‖^2 ≤ d)
    (hγ : ∀ j : Fin N, (4*((gaussianGlobalScoreConstant μ (2*η) d)^2/(4*d)+1))*‖v j.val‖^2 ≤
      (rowSquareExpExponent (4*d) (∫ x : ℝ, Real.exp (4*d*‖x‖^2) ∂μ))/8)
    (R : ℝ) (hR : 0 ≤ R) :
    (∫ x, ∑ j : Fin N, ‖gaussianRowRegression μ (2*η) v j t η x‖^2
      ∂gaussianFiniteRowLaw μ (2*η) (fun i : Fin N => v i.val) t) ≤
      (gaussianEntryTaylorConstant (2*η) R 1 (∫ z : ℝ, ‖z‖^3 ∂μ)+
        gaussianScoreComparisonConstant (2*η) R*
          ((∫ z : ℝ, ‖z‖^3 ∂μ)+(∫ z : ℝ, ‖z‖^3 ∂standardNormal))+R/η^2)^2*δ^2+
        gaussianRowRegressionTailBound μ (2*η) d η K R := by
  apply gaussianRowRegression_integral_le_of_compact μ hm hvar d hd hexp v hv
    (2*η) (by positivity) t K ht hsmall hγ η hη R hR _ δ
  intro j x hx
  exact real_gaussianRowRegression_flat_compact μ hm hvar (4*d) (by positivity) hexp
    v hv δ hflat j t η hη R hR x hx

/-- Fully instantiated finite expected row error for proper complex entries. -/
theorem complex_gaussianRowRegression_secondMoment (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℂ => Real.exp (4*d*‖x‖^2)) μ)
    (v : ℕ → ℂ) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (δ : ℝ) (hflat : ∀ j : Fin N, ‖v j.val‖ ≤ δ)
    (η : ℝ) (hη : 0 < η) (t : ℂ) (K : ℝ) (ht : ‖t‖ ≤ K)
    (hsmall : ∀ j : Fin N, gaussianGlobalScoreConstant μ η d*‖v j.val‖^2 ≤ d)
    (hγ : ∀ j : Fin N, (4*((gaussianGlobalScoreConstant μ η d)^2/(4*d)+1))*‖v j.val‖^2 ≤
      (rowSquareExpExponent (4*d) (∫ x : ℂ, Real.exp (4*d*‖x‖^2) ∂μ))/8)
    (R : ℝ) (hR : 0 ≤ R) :
    (∫ x, ∑ j : Fin N, ‖gaussianRowRegression μ η v j t η x‖^2
      ∂gaussianFiniteRowLaw μ η (fun i : Fin N => v i.val) t) ≤
      (gaussianEntryTaylorConstant η R (1/2) (∫ z : ℂ, ‖z‖^3 ∂μ)+
        ((1/2)*gaussianScoreComparisonConstant η R)*
          ((∫ z : ℂ, ‖z‖^3 ∂μ)+(∫ z : ℂ, ‖z‖^3 ∂properComplexGaussian))+R/η^2)^2*δ^2+
        gaussianRowRegressionTailBound μ η d η K R := by
  apply gaussianRowRegression_integral_le_of_compact μ hm hvar d hd hexp v hv
    η hη t K ht hsmall hγ η hη R hR _ δ
  intro j x hx
  exact complex_gaussianRowRegression_flat_compact μ hm hvar hpseudo (4*d) (by positivity) hexp
    v hv δ hflat j t η hη R hR x hx

#print axioms real_gaussianRowRegression_secondMoment
#print axioms complex_gaussianRowRegression_secondMoment
end SpectralRadiusUpperTail
