import SpectralRadiusUpperTail.ComplexSphereDiagonalization
import SpectralRadiusUpperTail.ComplexDiagonalWitness
import SpectralRadiusUpperTail.HermitianMinimumEnergy
import SpectralRadiusUpperTail.HermitianShiftDeterminant

namespace SpectralRadiusUpperTail
open scoped ENNReal ComplexOrder MatrixOrder

/-- The exponential-rate spherical witness for an actual positive semidefinite matrix. -/
lemma complex_sphere_witness (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ = 1) (d : ℝ)
    (hd : (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).re ≤ d) :
    ENNReal.ofReal (Real.exp (-(n : ℝ)*d/u-(n : ℝ))*u^n/
      ‖(H+((2*u : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖) ≤
        ENNReal.ofReal (sphereQuadraticIntegral ℂ n ((n : ℝ)/u) H) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨i, hi⟩ := hermitian_exists_minimum (by omega) H hH.isHermitian
  have hmin := (hermitian_minimum_le_energy H hH.isHermitian i hi v hv).trans hd
  have hdet : ‖(H+((2*u : ℝ) : ℂ) • (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℂ)).det‖ =
      ∏ j, (hH.isHermitian.eigenvalues j+2*u) := by
    convert! posSemidef_shift_det_norm H hH (2*u) (by positivity) using 1
  rw [complex_sphere_integral_diagonalization (m+1) (by omega) _
    (div_nonneg (Nat.cast_nonneg _) hu.le) H hH,
    hdet]
  apply le_trans _ (complex_diagonal_exponential_witness m u hu hH.isHermitian.eigenvalues
    hH.eigenvalues_nonneg i hi)
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Finset.prod_nonneg (fun j _ => by
    linarith [hH.eigenvalues_nonneg j]))
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hu.le _)
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hmin (show 0 ≤ ((m+1 : ℕ) : ℝ)/u by positivity)
  convert! sub_le_sub_right (neg_le_neg hmul) (((m+1 : ℕ) : ℝ)) using 1 <;> ring

#print axioms complex_sphere_witness
end SpectralRadiusUpperTail
