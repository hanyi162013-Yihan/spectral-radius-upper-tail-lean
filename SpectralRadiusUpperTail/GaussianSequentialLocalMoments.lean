import SpectralRadiusUpperTail.GaussianFutureDensity
import SpectralRadiusUpperTail.GaussianSequentialCentering
import SpectralRadiusUpperTail.UniformFutureErrorTail

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The actual error has mean zero under every actual transition kernel. -/
lemma gaussianSequentialIncrement_kernel_mean_zero (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂)
    (n : ℕ) (hn : n < N) (s : Fin n → 𝕂 × 𝕂) :
    (∫ p, gaussianSequentialIncrement μ v a N t n (s,p) ∂gaussianSequentialKernel μ v a N t n s) = 0 := by
  have : IsMarkovKernel (gaussianSequentialKernel μ v a N t n) :=
    gaussianSequentialKernel_markov μ v a ha N t n
  rw [gaussianSequentialIncrement_eq_kernelCentered μ hX hm v a ha N t n hn]
  exact integral_centered_eq_zero _ _
    (gaussianSequentialKernel_difference_mean μ hX hm v a ha N t n hn s).1

/-- Both quantitative local estimates hold for the actual sequential kernel
and its actual centered error, under explicit local perturbation conditions. -/
theorem gaussianSequentialIncrement_local_moments (μ : Measure 𝕂) [IsProbabilityMeasure μ]
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
      Real.exp (d*(‖x‖+‖x‖^2)) ∂μ) ≤ 1/2) :
    let κ := gaussianSequentialKernel μ v a N t n s
    let e := fun p => gaussianSequentialIncrement μ v a N t n (s,p)
    let M := ∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ
    (∫ p, ‖e p‖^2 ∂κ) ≤ 12*(u*(∫ x : 𝕂, (1+‖x‖^2)*(d*(‖x‖+‖x‖^2))*
      Real.exp (d*(‖x‖+‖x‖^2)) ∂μ)) ∧
      Integrable (fun p => Real.exp ((d/8)*‖e p‖^2)) κ ∧
      (∫ p, Real.exp ((d/8)*‖e p‖^2) ∂κ) ≤ ((2*Real.exp d*M+M)/2)^2 := by
  let q := t-revealedSum (fun i x => v i*x) N n (coordinateVector Prod.fst n s)
  let T := ContinuousLinearMap.mul ℝ 𝕂 (v (N-(n+1)))
  have henergy := current_future_energy v (⟨N-(n+1), by omega⟩ : Fin N) hv
  have hv' : ∑ i : Fin (N-(n+1)), ‖v i.val‖^2 ≤ 1 := by
    exact (le_add_of_nonneg_left (sq_nonneg ‖v (N-(n+1))‖)).trans henergy
  have hcouple := gaussianFuture_likelihood_coupling μ v (N-(n+1)) hX hm hvar hv'
    a d ha hd hexp q T u hu hu1 hsmall herror
  have htail := gaussianFuture_centered_squareExp μ v (N-(n+1)) hX hm hvar hv'
    a d ha hd hexp q T u hu hu1 hsmall herror
  have heq := gaussianSequentialKernel_eq_futureCoupling μ hX v N n hn a ha t s
  dsimp only [T, ContinuousLinearMap.mul_apply'] at hcouple htail
  rw [← heq] at hcouple htail
  have hmean := (gaussianSequentialKernel_difference_mean μ hX hm v a ha N t n hn s).2
  rw [hmean] at hcouple htail
  exact ⟨hcouple.2.2.2.2.2, htail.1, htail.2⟩

#print axioms gaussianSequentialIncrement_local_moments
end SpectralRadiusUpperTail
