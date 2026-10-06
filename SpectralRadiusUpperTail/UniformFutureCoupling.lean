import SpectralRadiusUpperTail.UniformFutureScore
import SpectralRadiusUpperTail.GaussianLikelihoodCoupling

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The actual recursive future likelihood has the normalized centered coupling
bound using only entry-law moment hypotheses. All future-law moments are derived.
The two explicit smallness inequalities set the local perturbation regime. -/
theorem gaussianFuture_likelihood_coupling (μ : Measure 𝕂) [IsProbabilityMeasure μ]
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
    let ε := u*(∫ x : 𝕂, (1+‖x‖^2)*(d*(‖x‖+‖x‖^2))*
      Real.exp (d*(‖x‖+‖x‖^2)) ∂μ)
    let W := futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N
    let g := fun x => (W (s-T x)).toReal/(W s).toReal
    let Z := ∫ x, g x ∂μ
    let k := fun x => g x/Z
    let π := densityCoupling μ (fun x => ENNReal.ofReal (k x))
    1/2 ≤ Z ∧ IsProbabilityMeasure π ∧
      π.map Prod.fst = μ.withDensity (fun x => ENNReal.ofReal (k x)) ∧
      π.map Prod.snd = μ ∧
      Integrable (fun z : 𝕂 × 𝕂 => z.1-z.2) π ∧
      (∫ z, ‖(z.1-z.2) - ∫ w, w.1-w.2 ∂π‖^2 ∂π) ≤ 12*ε := by
  have hXm := iidRowSumLaw_memLp μ v N hX
  have hmm := iidRowSumLaw_mean μ v N hX hm
  have hvm : (∫ x : 𝕂, ‖x‖^2 ∂iidRowSumLaw μ v N) ≤ 1 := by
    rw [iidRowSumLaw_energy μ v N hX hm hvar]
    exact hv
  obtain ⟨hc, he, hM⟩ := iidRowSumLaw_squareExp μ v N
    (hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hm hv (4*d) (by positivity) hexp
  have hLn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL : (∫ x : 𝕂, Real.exp
      (rowSquareExpExponent (4*d) (∫ y : 𝕂, Real.exp (4*d*‖y‖^2) ∂μ)*‖x‖^2)
        ∂iidRowSumLaw μ v N) ≤ Real.exp (Real.log 2) := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hM
  have h2 := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX
  have hh := gaussian_likelihood_coupling (iidRowSumLaw μ v N) μ hXm hmm hvm a _ (Real.log 2)
    ha hc hLn he hL d hd h2 hexp s T u hu hu1 hsmall herror
  have heq (t : 𝕂) :
      (futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N t).toReal =
        gaussianConvolution (iidRowSumLaw μ v N) a t := by
    rw [gaussianFutureWeight_eq_convolution μ v N a ha]
    exact ENNReal.toReal_ofReal (gaussianSoftTilt_basics _ hXm hmm a ha t).1.le
  dsimp only
  simp_rw [heq]
  dsimp only at hh
  rw [hvar] at hh
  have hnum (q : ℝ) : 4*q*(2+1) = 12*q := by ring
  rw [hnum] at hh
  exact hh

#print axioms gaussianFuture_likelihood_coupling
end SpectralRadiusUpperTail
