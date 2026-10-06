import SpectralRadiusUpperTail.ProductRowEnergy
import SpectralRadiusUpperTail.RowNormalizerBound
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {N : ℕ}

/-- The normalized iid matrix bilinear coefficient on the actual entry-product space. -/
noncomputable def iidBilinear (p q : Fin N → 𝕂) (x : Fin N × Fin N → 𝕂) : 𝕂 :=
  ∑ ij, (((1/Real.sqrt (N : ℝ) : ℝ) : 𝕂)*star (p ij.1)*q ij.2)*x ij

lemma iidBilinear_memLp (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (p q : Fin N → 𝕂) (hX : MemLp (fun x : 𝕂 => x) 2 μ) :
    MemLp (iidBilinear p q) 2 (Measure.pi (fun _ : Fin N × Fin N => μ)) := by
  exact iid_linear_row_memLp μ _ hX

/-- Exact second moment under independent entries; no independence of real and
imaginary parts, symmetry, or Gaussian entry assumption is imposed. -/
lemma iidBilinear_secondMoment (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (p q : Fin N → 𝕂) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hv : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) :
    (∫ x, ‖iidBilinear p q x‖^2 ∂Measure.pi (fun _ : Fin N × Fin N => μ)) =
      (1/(N : ℝ))*(∑ i, ‖p i‖^2)*(∑ j, ‖q j‖^2) := by
  unfold iidBilinear
  rw [iid_linear_row_energy μ _ hX hm hv]
  simp only [norm_mul, RCLike.norm_ofReal, norm_star, mul_pow, sq_abs, div_pow,
    one_pow, Real.sq_sqrt (Nat.cast_nonneg N), Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

#print axioms iidBilinear_memLp
#print axioms iidBilinear_secondMoment
end SpectralRadiusUpperTail
