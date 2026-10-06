import SpectralRadiusUpperTail.GaussianKernelTruncation

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Quantitative conditional truncation bounds on the actual kernel, derived
from the original entry assumptions and explicit local perturbation regime. -/
theorem gaussianTruncatedSequentialIncrement_local_bounds (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂) (N : ℕ)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : 𝕂) (n : ℕ) (hn : n < N) (s : Fin n → 𝕂 × 𝕂)
    (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hsmall : gaussianScoreConstant a
      (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)) (Real.log 2)*
      ‖ContinuousLinearMap.mul ℝ 𝕂 (v (N-(n+1)))‖*
      (1+‖t-revealedSum (fun i x => v i*x) N n (coordinateVector Prod.fst n s)‖+
        ‖ContinuousLinearMap.mul ℝ 𝕂 (v (N-(n+1)))‖) ≤ d*u)
    (herror : u*(∫ x : 𝕂, (1+‖x‖^2)*(d*(‖x‖+‖x‖^2))*
      Real.exp (d*(‖x‖+‖x‖^2)) ∂μ) ≤ 1/2)
    (R : ℝ) (hR : 0 ≤ R) :
    let κ := gaussianSequentialKernel μ v a N t n s
    let e := fun p => gaussianSequentialIncrement μ v a N t n (s,p)
    let eR := fun p => gaussianTruncatedSequentialIncrement μ v a N t n R (s,p)
    let M := ∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ
    (∫ p, ‖eR p‖^2 ∂κ) ≤ 12*(u*(∫ x : 𝕂, (1+‖x‖^2)*(d*(‖x‖+‖x‖^2))*
      Real.exp (d*(‖x‖+‖x‖^2)) ∂μ)) ∧
      (∫ p, ‖e p-eR p‖^2 ∂κ) ≤
        (16/d)*Real.exp (-(d/16)*R^2)*((2*Real.exp d*M+M)/2)^2 := by
  have hh := gaussianSequentialIncrement_local_moments μ hX hm hvar v N hv a d ha hd
    hexp t n hn s u hu hu1 hsmall herror
  have hc := gaussianTruncatedSequentialIncrement_conditional_moments μ hX hm v a ha N t
    n hn s (d/8) _ R (by positivity) hR hh.2.1 hh.2.2
  refine ⟨hc.1.trans hh.1, ?_⟩
  simpa only [show 2/(d/8) = 16/d by ring, show (d/8)/2 = d/16 by ring] using hc.2

#print axioms gaussianTruncatedSequentialIncrement_local_bounds
end SpectralRadiusUpperTail
