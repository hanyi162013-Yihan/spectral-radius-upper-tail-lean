import SpectralRadiusUpperTail.ComplexScaledSphereAverage
import SpectralRadiusUpperTail.FullSphereAnnealedSphereIdentity
import SpectralRadiusUpperTail.ComplexLightRowProduct

namespace SpectralRadiusUpperTail
open MeasureTheory Metric WithLp
open scoped ENNReal BigOperators

lemma complex_fullSphere_finite_bound_of_light (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hint : ∀ u : ℂ, Integrable (fun x : ℂ => Real.exp (2*(star u*x).re)) μ)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (n M : ℕ) (hn : 0 < n) (hMn : M ≤ n) (a K ε δ d : ℝ)
    (ha : 0 < a) (hK : 0 < K) (hε : 0 ≤ ε)
    (hδ : δ ≤ (Real.exp ε-1)*((a/(a+1))*Real.exp (-K^2/(a+1))))
    (hcard : ∀ v : Fin n → ℂ, (∑ j, ‖v j‖^2) = 1 → (largeCoordinateSet d v).card ≤ M)
    (hlight : ∀ v : Fin n → ℂ, (∑ j, ‖v j‖^2) = 1 → ∀ t : ℂ,
      gaussianFiniteNormalizer μ a v t ≤
        (a/(a+(largeCoordinateSet d v)ᶜ.sum (fun j => ‖v j‖^2)))*Real.exp (-‖t‖^2/(a+1))+δ)
    (z : ℂ) :
    (∫⁻ x : Fin n → Fin n → ℂ, fullSpectralSphereWeight n a z x
      ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) ≤
      ENNReal.ofReal (((M+1 : ℕ) : ℝ)*((n : ℝ)+1)^M*(a/(a+1))^(n-M)*
        Real.exp ((n : ℝ)*(-‖z‖^2/(a+1)+ε+(‖z‖^2/K^2)*(-Real.log (a/(a+1)))))) := by
  let B := (n : ℝ)*(-‖z‖^2/(a+1)+ε+(‖z‖^2/K^2)*(-Real.log (a/(a+1))))
  let D := ENNReal.ofReal (Real.exp B)
  let F := fun v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1 => ENNReal.ofReal
    (∏ i : Fin n, gaussianFiniteNormalizer μ a (ofLp v.val)
      (spectralTiltTarget z (zeroExtendVector (ofLp v.val)) i))
  have hF : Measurable F :=
    ((spectral_row_normalizer_product_measurable μ n a z).comp (by fun_prop)).ennreal_ofReal
  have hp := complex_varying_set_sphere_average_scaled n M hn hMn a ha D
    (ENNReal.ofReal_pos.mpr (Real.exp_pos B)).ne' ENNReal.ofReal_ne_top F hF (by
      intro v
      have hv : ∑ j, ‖v.val j‖^2 = 1 := by
        rw [← EuclideanSpace.norm_sq_eq, mem_sphere_zero_iff_norm.mp v.property]
        norm_num
      refine ⟨largeCoordinateSet d (ofLp v.val), hcard _ hv, ?_⟩
      have hh := complex_row_product_of_light_estimate μ hint hmgf n (ofLp v.val) hv
        (largeCoordinateSet d (ofLp v.val)) a K ε δ ha hK hε hδ (hlight _ hv) z
      have he := ENNReal.ofReal_le_ofReal hh
      rw [ENNReal.ofReal_mul (by positivity)] at he
      simpa only [F, D, B, mul_comm] using he)
  rw [fullSphere_annealed_sphere_identity μ n hn a ha z]
  apply hp.trans_eq
  dsimp only [D, B]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  ring

#print axioms complex_fullSphere_finite_bound_of_light
end SpectralRadiusUpperTail
