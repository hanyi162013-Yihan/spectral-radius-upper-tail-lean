import SpectralRadiusUpperTail.SphereInversePowerDeterminant
import SpectralRadiusUpperTail.PositiveDiagonalEnergy
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal BigOperators

lemma complex_diagonal_inverse_power (n : ℕ) (hn : 0 < n) (h : Fin n → ℝ)
    (hh : ∀ i, 0 < h i) :
    (∫⁻ v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1,
      ENNReal.ofReal ((∑ i, h i*‖v.val i‖^2)^n)⁻¹
      ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))) =
        ENNReal.ofReal ((∏ i, h i)⁻¹) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let A := (Matrix.toEuclideanCLM (𝕜 := ℂ) (positiveDiagonalRoot h)).toLinearMap.restrictScalars ℝ
  have hdet : LinearMap.det A = ∏ i, h i := by
    rw [complex_real_determinant, positiveDiagonalRoot_det_norm_sq h (fun i => (hh i).le)]
  have hp : 0 < ∏ i, h i := Finset.prod_pos (fun i _ => hh i)
  have hpos (v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1) : 0 < ‖A v.val‖ := by
    have he := positiveDiagonalRoot_energy h (fun i => (hh i).le) v.val
    have hb := positive_weighted_unit_energy h hh v.val (mem_sphere_zero_iff_norm.mp v.property)
    change 0 < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (positiveDiagonalRoot h) v.val‖
    nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (positiveDiagonalRoot h) v.val)]
  have hz := sphere_inverse_power_determinant
    (volume : Measure (EuclideanSpace ℂ (Fin n))) A (by rw [hdet]; exact hp.ne') hpos
  have hd : Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2*n := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin n))]
    simp
  rw [hd, hdet, abs_of_pos (inv_pos.mpr hp)] at hz
  rw [← hz]
  apply lintegral_congr
  intro v
  have he : ‖A v.val‖^(2*n) = (∑ i, h i*‖v.val i‖^2)^n := by
    rw [pow_mul]
    congr 1
    exact positiveDiagonalRoot_energy h (fun i => (hh i).le) v.val
  rw [he, ENNReal.ofReal_inv_of_pos (pow_pos
    (positive_weighted_unit_energy h hh v.val (mem_sphere_zero_iff_norm.mp v.property)) n)]

#print axioms complex_diagonal_inverse_power
end SpectralRadiusUpperTail
