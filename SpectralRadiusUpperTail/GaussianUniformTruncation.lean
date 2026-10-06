import SpectralRadiusUpperTail.GaussianTruncationScale
import SpectralRadiusUpperTail.GaussianSafeHistory

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- A common target cutoff and coefficient threshold give a conditional
variance bound proportional to the current coefficient on the actual kernel. -/
theorem gaussianTruncatedSequentialIncrement_uniform_bounds
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂) (N : ℕ)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : 𝕂) (n : ℕ) (hn : n < N) (s : Fin n → 𝕂 × 𝕂)
    (K δ R : ℝ) (hK : 0 ≤ K) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ‖v (N-(n+1))‖ ≤ δ)
    (hq : ‖t-revealedSum (fun i x => v i*x) N n (coordinateVector Prod.fst n s)‖ ≤ K)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2) :
    (∫ p, ‖gaussianTruncatedSequentialIncrement μ v a N t n R (s,p)‖^2
      ∂gaussianSequentialKernel μ v a N t n s) ≤
        (12*gaussianTruncationScale μ a d K*gaussianLocalMomentCost μ d)*‖v (N-(n+1))‖ ∧
      (∫ p, ‖gaussianSequentialIncrement μ v a N t n (s,p)-
        gaussianTruncatedSequentialIncrement μ v a N t n R (s,p)‖^2
        ∂gaussianSequentialKernel μ v a N t n s) ≤
          (16/d)*Real.exp (-(d/16)*R^2)*gaussianErrorExpBound μ d := by
  let C := gaussianScoreConstant a
    (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)) (Real.log 2)
  let b := ‖v (N-(n+1))‖
  let q := t-revealedSum (fun i x => v i*x) N n (coordinateVector Prod.fst n s)
  have hC : 0 ≤ C := by dsimp [C, gaussianScoreConstant]; positivity
  have hs := localCoefficientSmallness C K d (gaussianLocalMomentCost μ d) δ b ‖q‖ hC hK hd
    (gaussianLocalMomentCost_nonneg μ d hd.le) (norm_nonneg _) hb hδ hq hunit herror
  have hsmall : C*‖ContinuousLinearMap.mul ℝ 𝕂 (v (N-(n+1)))‖*
      (1+‖q‖+‖ContinuousLinearMap.mul ℝ 𝕂 (v (N-(n+1)))‖) ≤
        d*(gaussianTruncationScale μ a d K*b) := by
    simpa only [ContinuousLinearMap.opNorm_mul_apply, b, C, gaussianTruncationScale] using hs.2.2.1
  have hh := gaussianTruncatedSequentialIncrement_local_bounds μ hX hm hvar v N hv a d ha hd
    hexp t n hn s (gaussianTruncationScale μ a d K*b) hs.1 hs.2.1 hsmall hs.2.2.2 R hR
  refine ⟨hh.1.trans_eq ?_, hh.2⟩
  change 12*((gaussianTruncationScale μ a d K*b)*gaussianLocalMomentCost μ d) = _
  dsimp [b]
  ring

/-- Every history selected by the actual predictable safe event satisfies the
uniform conditional variance and truncation-error estimates. -/
theorem gaussianTruncatedSequentialIncrement_safe_bounds
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂) (N : ℕ)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : 𝕂) (n : ℕ) (hn : n < N) (K δ R : ℝ) (hK : 0 ≤ K) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ‖v (N-(n+1))‖ ≤ δ)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2)
    (x : Fin N → 𝕂 × 𝕂) (hx : x ∈ prefixSafeEvent (gaussianTerminalTarget v N t) K n) :
    let s := pathSuffix N n hn.le x
    (∫ p, ‖gaussianTruncatedSequentialIncrement μ v a N t n R (s,p)‖^2
      ∂gaussianSequentialKernel μ v a N t n s) ≤
        (12*gaussianTruncationScale μ a d K*gaussianLocalMomentCost μ d)*‖v (N-(n+1))‖ ∧
      (∫ p, ‖gaussianSequentialIncrement μ v a N t n (s,p)-
        gaussianTruncatedSequentialIncrement μ v a N t n R (s,p)‖^2
        ∂gaussianSequentialKernel μ v a N t n s) ≤
          (16/d)*Real.exp (-(d/16)*R^2)*gaussianErrorExpBound μ d :=
  gaussianTruncatedSequentialIncrement_uniform_bounds μ hX hm hvar v N hv a d ha hd hexp t n hn
    (pathSuffix N n hn.le x) K δ R hK hδ hR hb
    (gaussianSafeHistory_target_bound v N t n hn.le K x hx) hunit herror

#print axioms gaussianTruncatedSequentialIncrement_safe_bounds
end SpectralRadiusUpperTail
