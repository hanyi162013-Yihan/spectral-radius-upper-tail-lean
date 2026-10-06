import SpectralRadiusUpperTail.GaussianTerminalPrefixMoment
import SpectralRadiusUpperTail.PrefixExponentialProbability

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The probability that any actual prefix triggers stopping is controlled by
the proved uniform tilted-row moments and a finite union bound. -/
theorem gaussianStoppedRow_bad_probability (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (τ : ℝ) (hτ : 0 < τ) (hexp : Integrable (fun x : 𝕂 => Real.exp (τ*‖x‖^2)) μ)
    (v : ℕ → 𝕂) (N : ℕ) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (a : ℝ) (ha : 0 < a) (t : 𝕂) (K : ℝ) (ht : ‖t‖ ≤ K)
    (R : ℝ) (hR : 0 ≤ R) :
    let c := rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)
    (gaussianSequentialRowLaw μ v a N t N).real
      (prefixSafeEvent (gaussianTerminalTarget v N t) R N)ᶜ ≤
        (N+1 : ℕ)*((2*Real.exp ((K^2+1)/a+c*K^2))*Real.exp (-(c/2)*R^2)) := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t N) :=
    gaussianSequentialRowLaw_probability μ v a ha N t N
  have hh (n : ℕ) (hn : n ≤ N) :=
    gaussianTerminalTarget_squareExp μ hm hvar τ hτ hexp v N hv a ha t K ht n hn
  exact prefixSafeEvent_compl_probability _ _ _ _ _
    (div_nonneg (hh 0 (Nat.zero_le N)).1.le (by norm_num)) hR N
    (fun n hn => (hh n hn).2.1) (fun n hn => (hh n hn).2.2)

#print axioms gaussianStoppedRow_bad_probability
end SpectralRadiusUpperTail
