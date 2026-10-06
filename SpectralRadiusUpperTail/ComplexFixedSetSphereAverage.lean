import SpectralRadiusUpperTail.ComplexDiagonalInversePower
import SpectralRadiusUpperTail.TwoLevelDiagonal

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal BigOperators

/-- The fixed-set beta integral, obtained directly from the ellipsoid identity. -/
lemma complex_fixed_set_sphere_average (n : ℕ) (hn : 0 < n) (I : Finset (Fin n))
    (c : ℝ) (hc : 0 < c) :
    (∫⁻ v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1,
      ENNReal.ofReal ((c/(c+Iᶜ.sum (fun j => ‖v.val j‖^2)))^n)
      ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))) =
        ENNReal.ofReal ((c/(c+1))^(n-I.card)) := by
  have hp (v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1) :
      0 < c+Iᶜ.sum (fun j => ‖v.val j‖^2) :=
    add_pos_of_pos_of_nonneg hc (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have he (v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1) :
      ENNReal.ofReal ((c/(c+Iᶜ.sum (fun j => ‖v.val j‖^2)))^n) =
        ENNReal.ofReal (c^n)*ENNReal.ofReal ((∑ j, twoLevelDiagonal I c j*‖v.val j‖^2)^n)⁻¹ := by
    rw [twoLevelDiagonal_energy I c v.val (mem_sphere_zero_iff_norm.mp v.property), div_pow,
      ENNReal.ofReal_div_of_pos (pow_pos (hp v) n), div_eq_mul_inv,
      ENNReal.ofReal_inv_of_pos (pow_pos (hp v) n)]
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop),
    complex_diagonal_inverse_power n hn (twoLevelDiagonal I c) (twoLevelDiagonal_pos I c hc),
    ← ENNReal.ofReal_mul (pow_nonneg hc.le n), twoLevelDiagonal_ratio I c hc]

#print axioms complex_fixed_set_sphere_average
end SpectralRadiusUpperTail
