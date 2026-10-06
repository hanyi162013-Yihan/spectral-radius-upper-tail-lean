import SpectralRadiusUpperTail.HaarFlatWeightCost
import SpectralRadiusUpperTail.SphereResidualWeight
import SpectralRadiusUpperTail.ComplexSphereRate
import SpectralRadiusUpperTail.LikelihoodCostAlgebra
import SpectralRadiusUpperTail.FlatSpectralLikelihood
import SpectralRadiusUpperTail.TiltNormalizerRate

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology ENNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

lemma complex_likelihood_cost_on_bulk
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (c*‖x‖^2)) μ)
    (u ell κ δ b : ℝ) (hu : 0 < u) (hell : 0 < ell) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ (L : ℝ) (hL : 1 ≤ L), ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → Fin n → ℂ,
      2*Real.log b-δ ≤ regularizedResidualLogDet x (b : ℂ) (ell*u)/(n : ℝ) →
      flatSpectralMatrixLikelihood μ (haarFlatPrior ℂ n L hL) u (b : ℂ) x ≤
        ENNReal.ofReal (Real.exp ((n : ℝ)*lowerTiltCost 2 b u (ell+δ) κ (2*δ))) := by
  obtain ⟨L,hL,hw⟩ := complex_flatHaar_weight_cost κ hκ
  let ν : (n : ℕ) → Measure (flatUnitDirections ℂ n L) := fun n => haarFlatPrior ℂ n L hL
  letI : ∀ n, IsProbabilityMeasure (ν n) := fun n => haarFlatPrior_probability ℂ n L hL
  let Z : ℕ → ℝ := fun n => ∫ p, flatSpectralJointWeight u (b : ℂ) p
    ∂(ν n).prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
  have hz (n : ℕ) : 0 < Z n := integral_exp_pos
    (flatSpectralJointWeight_integrable μ (ν n) u hu (b : ℂ))
  have ht := complex_manuscript_annealed_limit μ hm hvar hpseudo c hc hexp u hu L (by linarith) ν b
  have hnorm := (tendsto_order.1 ht).1 (annealedTiltRate 2 b u-δ) (by linarith)
  refine ⟨L,hL,?_⟩
  filter_upwards [hw,hnorm,complex_sphere_rate_upper u ell δ hu hell hδ,eventually_ge_atTop (1 : ℕ)]
    with n hwn hzn hsn hn1
  have hn : 0 < n := by omega
  intro x hx
  let I := sphereQuadraticIntegral ℂ n ((n : ℝ)/u) (spectralResidualGram x (b : ℂ))
  have hi : 0 < I := sphereQuadraticIntegral_pos ℂ n hn _
    (div_nonneg (Nat.cast_nonneg n) hu.le) _ (spectralResidualGram_posSemidef x (b : ℂ))
  have hweight := hwn u (b : ℂ) x
  rw [fullSphereWeight_eq_quadratic n hn u hu] at hweight
  have hsp := hsn (spectralResidualGram x (b : ℂ)) (spectralResidualGram_posSemidef x (b : ℂ))
  change Real.log I/(n : ℝ) ≤ Real.log u+ell-1-
    regularizedResidualLogDet x (b : ℂ) (ell*u)/(n : ℝ)+δ at hsp
  have hS : Real.log I/(n : ℝ) ≤ Real.log u+(ell+δ-1)-2*Real.log b+δ := by linarith
  have hh := likelihood_cost_of_log_bounds n hn
    (flatSpectralMatrixWeight (ν n) u (b : ℂ) x) I (Z n) κ
    (Real.log u+(ell+δ-1)-2*Real.log b+δ) (annealedTiltRate 2 b u-δ)
    hi (hz n) hweight hS hzn.le
  have he : κ+(Real.log u+(ell+δ-1)-2*Real.log b+δ)-(annealedTiltRate 2 b u-δ) =
      lowerTiltCost 2 b u (ell+δ) κ (2*δ) := by
    convert spherical_minus_annealed_cost 2 b u (ell+δ) κ (2*δ) hu using 1 <;> ring
  rw [he] at hh
  change flatSpectralMatrixWeight (ν n) u (b : ℂ) x /
    (∫⁻ y, flatSpectralMatrixWeight (ν n) u (b : ℂ) y
      ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) ≤ _
  rw [flatSpectralMatrixWeight_normalizer μ (ν n) u hu]
  exact hh

#print axioms complex_likelihood_cost_on_bulk
end SpectralRadiusUpperTail
