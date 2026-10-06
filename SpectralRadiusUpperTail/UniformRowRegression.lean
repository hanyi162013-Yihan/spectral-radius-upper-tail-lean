import SpectralRadiusUpperTail.GaussianRegressionScales

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- A common compact coefficient bound upgrades the actual finite row result
to a uniform modulus. Both field-specific compact estimates are instantiated below. -/
theorem gaussianRowRegression_uniform_of_compact (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (a η K : ℝ) (ha : 0 < a) (hη : 0 < η) (C : ℝ → ℝ)
    (hcompact : ∀ R : ℝ, 0 ≤ R → ∀ (N : ℕ) (v : ℕ → 𝕂),
      (∑ i : Fin N, ‖v i.val‖^2) ≤ 1 → ∀ δ : ℝ, (∀ j : Fin N, ‖v j.val‖ ≤ δ) →
      ∀ (j : Fin N) (t : 𝕂) (x : Fin N → 𝕂), ‖upperRowTarget v j t x‖ ≤ R →
        ‖gaussianRowRegression μ a v j t η x‖ ≤ C R*δ*‖v j.val‖)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (v : ℕ → 𝕂), (∑ j : Fin N, ‖v j.val‖^2) ≤ 1 →
      (∀ j : Fin N, ‖v j.val‖ ≤ δ) → ∀ t : 𝕂, ‖t‖ ≤ K →
      Integrable (fun x => ∑ j : Fin N, ‖gaussianRowRegression μ a v j t η x‖^2)
        (gaussianFiniteRowLaw μ a (fun i : Fin N => v i.val) t) ∧
      (∫ x, ∑ j : Fin N, ‖gaussianRowRegression μ a v j t η x‖^2
        ∂gaussianFiniteRowLaw μ a (fun i : Fin N => v i.val) t) < ε := by
  obtain ⟨R, hR, δ, hδ, h₁, h₂, hε'⟩ := exists_gaussian_regression_scales μ a d η K ha hd C ε hε
  refine ⟨δ, hδ, ?_⟩
  intro N v hv hflat t ht
  have hb (j : Fin N) := gaussian_regression_coefficient_thresholds μ a d δ ha hd hδ.le h₁ h₂
    (v j.val) (hflat j)
  refine ⟨(gaussianRowRegression_sum_tail μ hm hvar d hd hexp v hv a ha t K ht
    (fun j => (hb j).1) (fun j => (hb j).2) η hη R hR).1, ?_⟩
  exact (gaussianRowRegression_integral_le_of_compact μ hm hvar d hd hexp v hv a ha t K ht
    (fun j => (hb j).1) (fun j => (hb j).2) η hη R hR (C R) δ
    (fun j x hx => hcompact R hR N v hv δ hflat j t x hx)).trans_lt hε'

/-- The actual real regression error vanishes uniformly with the maximum
coefficient, across all dimensions and all targets in a fixed bounded set. -/
theorem real_gaussianRowRegression_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℝ => Real.exp (4*d*‖x‖^2)) μ)
    (η K : ℝ) (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (v : ℕ → ℝ), (∑ j : Fin N, ‖v j.val‖^2) ≤ 1 →
      (∀ j : Fin N, ‖v j.val‖ ≤ δ) → ∀ t : ℝ, ‖t‖ ≤ K →
      Integrable (fun x => ∑ j : Fin N, ‖gaussianRowRegression μ (2*η) v j t η x‖^2)
        (gaussianFiniteRowLaw μ (2*η) (fun i : Fin N => v i.val) t) ∧
      (∫ x, ∑ j : Fin N, ‖gaussianRowRegression μ (2*η) v j t η x‖^2
        ∂gaussianFiniteRowLaw μ (2*η) (fun i : Fin N => v i.val) t) < ε := by
  apply gaussianRowRegression_uniform_of_compact μ hm hvar d hd hexp (2*η) η K (by positivity) hη
    (fun R => gaussianEntryTaylorConstant (2*η) R 1 (∫ z : ℝ, ‖z‖^3 ∂μ)+
      gaussianScoreComparisonConstant (2*η) R*
        ((∫ z : ℝ, ‖z‖^3 ∂μ)+(∫ z : ℝ, ‖z‖^3 ∂standardNormal))+R/η^2) _ ε hε
  intro R hR N v hv δ hflat j t x hx
  exact real_gaussianRowRegression_flat_compact μ hm hvar (4*d) (by positivity) hexp v hv δ hflat
    j t η hη R hR x hx

/-- Proper-complex uniform vanishing uses no independence of the original
entry's real and imaginary parts. -/
theorem complex_gaussianRowRegression_uniform (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℂ => Real.exp (4*d*‖x‖^2)) μ)
    (η K : ℝ) (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (v : ℕ → ℂ), (∑ j : Fin N, ‖v j.val‖^2) ≤ 1 →
      (∀ j : Fin N, ‖v j.val‖ ≤ δ) → ∀ t : ℂ, ‖t‖ ≤ K →
      Integrable (fun x => ∑ j : Fin N, ‖gaussianRowRegression μ η v j t η x‖^2)
        (gaussianFiniteRowLaw μ η (fun i : Fin N => v i.val) t) ∧
      (∫ x, ∑ j : Fin N, ‖gaussianRowRegression μ η v j t η x‖^2
        ∂gaussianFiniteRowLaw μ η (fun i : Fin N => v i.val) t) < ε := by
  apply gaussianRowRegression_uniform_of_compact μ hm hvar d hd hexp η η K hη hη
    (fun R => gaussianEntryTaylorConstant η R (1/2) (∫ z : ℂ, ‖z‖^3 ∂μ)+
      ((1/2)*gaussianScoreComparisonConstant η R)*
        ((∫ z : ℂ, ‖z‖^3 ∂μ)+(∫ z : ℂ, ‖z‖^3 ∂properComplexGaussian))+R/η^2) _ ε hε
  intro R hR N v hv δ hflat j t x hx
  exact complex_gaussianRowRegression_flat_compact μ hm hvar hpseudo (4*d) (by positivity) hexp v hv δ hflat
    j t η hη R hR x hx

#print axioms real_gaussianRowRegression_uniform
#print axioms complex_gaussianRowRegression_uniform
end SpectralRadiusUpperTail
