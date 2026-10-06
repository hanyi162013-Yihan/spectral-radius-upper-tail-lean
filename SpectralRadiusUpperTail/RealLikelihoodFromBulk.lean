import SpectralRadiusUpperTail.HaarFlatWeightCost
import SpectralRadiusUpperTail.SphereResidualWeight
import SpectralRadiusUpperTail.RealSphereRate
import SpectralRadiusUpperTail.LikelihoodCostAlgebra
import SpectralRadiusUpperTail.FlatSpectralLikelihood
import SpectralRadiusUpperTail.TiltNormalizerRate

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology ENNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

lemma real_likelihood_cost_on_bulk
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ)
    (u ell κ δ b : ℝ) (hu : 0 < u) (hell : 0 < ell) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ (L : ℝ) (hL : 1 ≤ L), ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → Fin n → ℝ,
      2*Real.log b-δ ≤ regularizedResidualLogDet x (b : ℝ) (ell*u)/(n : ℝ) →
      flatSpectralMatrixLikelihood μ (haarFlatPrior ℝ n L hL) (2*u) (b : ℝ) x ≤
        ENNReal.ofReal (Real.exp ((n : ℝ)*lowerTiltCost 1 b u (ell+δ) κ (2*δ))) := by
  obtain ⟨L,hL,hw⟩ := real_flatHaar_weight_cost κ hκ
  let ν : (n : ℕ) → Measure (flatUnitDirections ℝ n L) := fun n => haarFlatPrior ℝ n L hL
  letI : ∀ n, IsProbabilityMeasure (ν n) := fun n => haarFlatPrior_probability ℝ n L hL
  let Z : ℕ → ℝ := fun n => ∫ p, flatSpectralJointWeight (2*u) (b : ℝ) p
    ∂(ν n).prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
  have hz (n : ℕ) : 0 < Z n := integral_exp_pos
    (flatSpectralJointWeight_integrable μ (ν n) (2*u) (by positivity) (b : ℝ))
  have ht := real_manuscript_annealed_limit μ hm hvar c hc hexp u hu L (by linarith) ν b
  have hnorm := (tendsto_order.1 ht).1 (annealedTiltRate 1 b u-δ) (by linarith)
  refine ⟨L,hL,?_⟩
  filter_upwards [hw,hnorm,real_sphere_rate_upper u ell δ hu hell hδ,eventually_ge_atTop (1 : ℕ)]
    with n hwn hzn hsn hn1
  have hn : 0 < n := by omega
  intro x hx
  let I := sphereQuadraticIntegral ℝ n ((n : ℝ)/(2*u)) (spectralResidualGram x (b : ℝ))
  have hi : 0 < I := sphereQuadraticIntegral_pos ℝ n hn _
    (div_nonneg (Nat.cast_nonneg n) (by positivity)) _ (spectralResidualGram_posSemidef x (b : ℝ))
  have hweight := hwn (2*u) (b : ℝ) x
  rw [fullSphereWeight_eq_quadratic n hn (2*u) (by positivity)] at hweight
  have hsp := hsn (spectralResidualGram x (b : ℝ)) (spectralResidualGram_posSemidef x (b : ℝ))
  change Real.log I/(n : ℝ) ≤ (Real.log u+ell-1)/2-
    regularizedResidualLogDet x (b : ℝ) (ell*u)/(2*(n : ℝ))+δ at hsp
  have hdiv : regularizedResidualLogDet x (b : ℝ) (ell*u)/(2*(n : ℝ)) =
      (regularizedResidualLogDet x (b : ℝ) (ell*u)/(n : ℝ))/2 := by ring
  rw [hdiv] at hsp
  have hS : Real.log I/(n : ℝ) ≤ (Real.log u+(ell+δ-1))/2-Real.log b+δ := by linarith
  have hh := likelihood_cost_of_log_bounds n hn
    (flatSpectralMatrixWeight (ν n) (2*u) (b : ℝ) x) I (Z n) κ
    ((Real.log u+(ell+δ-1))/2-Real.log b+δ) (annealedTiltRate 1 b u-δ)
    hi (hz n) hweight hS hzn.le
  have he : κ+((Real.log u+(ell+δ-1))/2-Real.log b+δ)-(annealedTiltRate 1 b u-δ) =
      lowerTiltCost 1 b u (ell+δ) κ (2*δ) := by
    convert spherical_minus_annealed_cost 1 b u (ell+δ) κ (2*δ) hu using 1 <;> ring
  rw [he] at hh
  change flatSpectralMatrixWeight (ν n) (2*u) (b : ℝ) x /
    (∫⁻ y, flatSpectralMatrixWeight (ν n) (2*u) (b : ℝ) y
      ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) ≤ _
  rw [flatSpectralMatrixWeight_normalizer μ (ν n) (2*u) (by positivity)]
  exact hh

#print axioms real_likelihood_cost_on_bulk
end SpectralRadiusUpperTail
