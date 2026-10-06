import SpectralRadiusUpperTail.GaussianLikelihoodError
import SpectralRadiusUpperTail.NormalizedCoupling

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Actual Gaussian likelihoods satisfy the quantitative centered coupling
bound. Uniform future-sum moments and regression estimates remain separate. -/
theorem gaussian_likelihood_coupling
    (ν μ : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 ν) (hm : (∫ x : E, x ∂ν) = 0)
    (hvar : (∫ x : E, ‖x‖^2 ∂ν) ≤ 1) (a c L : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hLn : 0 ≤ L)
    (hexp : Integrable (fun x : E => Real.exp (c*‖x‖^2)) ν)
    (hL : (∫ x : E, Real.exp (c*‖x‖^2) ∂ν) ≤ Real.exp L)
    (d : ℝ) (hd : 0 < d)
    (h2 : Integrable (fun x : E => ‖x‖^2) μ)
    (hentry : Integrable (fun x : E => Real.exp (4*d*‖x‖^2)) μ)
    (s : E) (T : E →L[ℝ] E) (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hsmall : gaussianScoreConstant a c L*‖T‖*(1+‖s‖+‖T‖) ≤ d*u)
    (herror : u*(∫ x, (1+‖x‖^2)*(d*(‖x‖+‖x‖^2))*
      Real.exp (d*(‖x‖+‖x‖^2)) ∂μ) ≤ 1/2) :
    let ε := u*(∫ x, (1+‖x‖^2)*(d*(‖x‖+‖x‖^2))*
      Real.exp (d*(‖x‖+‖x‖^2)) ∂μ)
    let g := fun x => gaussianConvolution ν a (s-T x)/gaussianConvolution ν a s
    let Z := ∫ x, g x ∂μ
    let k := fun x => g x/Z
    let π := densityCoupling μ (fun x => ENNReal.ofReal (k x))
    1/2 ≤ Z ∧ IsProbabilityMeasure π ∧
      π.map Prod.fst = μ.withDensity (fun x => ENNReal.ofReal (k x)) ∧
      π.map Prod.snd = μ ∧
      Integrable (fun z : E × E => z.1-z.2) π ∧
      (∫ z, ‖(z.1-z.2) - ∫ w, w.1-w.2 ∂π‖^2 ∂π) ≤
        4*ε*(2+∫ x : E, ‖x‖^2 ∂μ) := by
  obtain ⟨hg, hgi, hei, herr⟩ := gaussian_likelihood_weighted_error ν μ hX hm hvar
    a c L ha hc hLn hexp hL d hd hentry s T u hu hu1 hsmall
  have hgn (x : E) : 0 ≤ gaussianConvolution ν a (s-T x)/gaussianConvolution ν a s :=
    div_nonneg (gaussianSoftTilt_basics ν hX hm a ha (s-T x)).1.le
      (gaussianSoftTilt_basics ν hX hm a ha s).1.le
  have hε : 0 ≤ u*(∫ x, (1+‖x‖^2)*(d*(‖x‖+‖x‖^2))*
      Real.exp (d*(‖x‖+‖x‖^2)) ∂μ) :=
    mul_nonneg hu (integral_nonneg (fun x => by positivity))
  exact normalized_likelihood_coupling μ _ hg hgi hgn h2 hei _ hε herror herr

#print axioms gaussian_likelihood_coupling
end SpectralRadiusUpperTail
