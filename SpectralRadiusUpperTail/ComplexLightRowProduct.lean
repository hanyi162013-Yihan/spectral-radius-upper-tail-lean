import SpectralRadiusUpperTail.ComplexSharpRowMGF
import SpectralRadiusUpperTail.CoordinateMaskEnergy
import SpectralRadiusUpperTail.SoftRowProductBound
import SpectralRadiusUpperTail.SpectralTiltTargetEnergy

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma complex_row_product_of_light_estimate (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hint : ∀ u : ℂ, Integrable (fun x : ℂ => Real.exp (2*(star u*x).re)) μ)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (n : ℕ) (v : Fin n → ℂ) (hv : ∑ j, ‖v j‖^2 = 1) (I : Finset (Fin n))
    (a K ε δ : ℝ) (ha : 0 < a) (hK : 0 < K) (hε : 0 ≤ ε)
    (hδ : δ ≤ (Real.exp ε-1)*((a/(a+1))*Real.exp (-K^2/(a+1))))
    (hlight : ∀ t : ℂ, gaussianFiniteNormalizer μ a v t ≤
      (a/(a+Iᶜ.sum (fun j => ‖v j‖^2)))*Real.exp (-‖t‖^2/(a+1))+δ)
    (z : ℂ) :
    (∏ i : Fin n, gaussianFiniteNormalizer μ a v (spectralTiltTarget z (zeroExtendVector v) i)) ≤
      (a/(a+Iᶜ.sum (fun j => ‖v j‖^2)))^n*
        Real.exp ((n : ℝ)*(-‖z‖^2/(a+1)+ε+(‖z‖^2/K^2)*(-Real.log (a/(a+1))))) := by
  let t : Fin n → ℂ := spectralTiltTarget z (zeroExtendVector v)
  obtain ⟨hq, hq1⟩ := complement_coordinate_energy_bounds I v hv.le
  have hrow (i : Fin n) := soft_row_error_bound (gaussianFiniteNormalizer μ a v (t i)) a
    (Iᶜ.sum (fun j => ‖v j‖^2)) (‖t i‖^2) K ε δ ha hq hq1 (sq_nonneg _) hK hε
    (by simpa only [hv] using complex_sharp_row_soft μ hint hmgf n v a ha (t i)) (hlight (t i)) hδ
  have hh := soft_row_product_bound n (fun i => gaussianFiniteNormalizer μ a v (t i))
    (fun i => ‖t i‖^2) (a/(a+Iᶜ.sum (fun j => ‖v j‖^2))) a K ε (-Real.log (a/(a+1)))
    (fun i => integral_nonneg (fun _ => Real.exp_nonneg _)) hrow
  have he : ∑ i, ‖t i‖^2 = (n : ℝ)*‖z‖^2 :=
    spectralTiltTarget_energy (n := n) z (zeroExtendVector v) (by simpa only [zeroExtendVector_fin] using hv)
  rw [he] at hh
  convert! hh using 1
  congr 2
  ring

#print axioms complex_row_product_of_light_estimate
end SpectralRadiusUpperTail
