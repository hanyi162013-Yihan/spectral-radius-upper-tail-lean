import SpectralRadiusUpperTail.RealPairNonrealCoordinates
import SpectralRadiusUpperTail.RealSchurPairRotation
import SpectralRadiusUpperTail.MatrixUnitaryFrobenius

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius

theorem realSchurRotation_orthogonal (θ : ℝ) :
    (realSchurRotation θ)ᵀ*realSchurRotation θ=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSchurRotation,Matrix.mul_apply,Fin.sum_univ_two,
      Real.sin_sq_add_cos_sq,Real.cos_sq_add_sin_sq,pow_two] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Rotating the canonical pair changes only the angle of its symmetric
traceless part. The skew coordinate q is preserved. -/
theorem realSchurRotation_cartesian (θ x r q : ℝ) :
    realSchurRotation θ * realSchurBlock x (q+r) (q-r) * (realSchurRotation θ)ᵀ =
      realPairCartesianMatrix x (-r*Real.sin (2*θ)) (r*Real.cos (2*θ)) q := by
  rw [realSchurRotation_conjugate_block]
  have hs : Real.sin θ^2=1-Real.cos θ^2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSchurRotatedBlock,realPairCartesianMatrix,Real.sin_two_mul,Real.cos_two_mul,hs] <;> ring

theorem realPairPolarMatrix_conjugate (φ x r q : ℝ) :
    realPairCartesianMatrix x (r*Real.cos φ) (r*Real.sin φ) q =
      realSchurRotation ((φ-Real.pi/2)/2) * realSchurBlock x (q+r) (q-r) *
        (realSchurRotation ((φ-Real.pi/2)/2))ᵀ := by
  rw [realSchurRotation_cartesian]
  have ht : 2*((φ-Real.pi/2)/2)=φ-Real.pi/2 := by ring
  rw [ht,Real.sin_sub,Real.cos_sub]
  simp [Real.sin_pi_div_two,Real.cos_pi_div_two]

/-- The full power energy of a nonreal pair is independent of the
internal angular coordinate, including both signs of its skew part. -/
theorem realPairPolarMatrix_power_energy (φ x r q : ℝ) (k : ℕ) :
    ‖(realPairCartesianMatrix x (r*Real.cos φ) (r*Real.sin φ) q)^k‖^2 =
      ‖(realSchurBlock x (q+r) (q-r))^k‖^2 := by
  let Q := realSchurRotation ((φ-Real.pi/2)/2)
  have hQ : Q ∈ Matrix.unitaryGroup (Fin 2) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using realSchurRotation_orthogonal ((φ-Real.pi/2)/2)
  have h := matrix_unitary_conjugation_power_frobenius_sq
    (realSchurBlock x (q+r) (q-r)) (⟨Q,hQ⟩ : Matrix.unitaryGroup (Fin 2) ℝ) k
  rw [realPairPolarMatrix_conjugate]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

#print axioms realSchurRotation_orthogonal
#print axioms realSchurRotation_cartesian
#print axioms realPairPolarMatrix_conjugate
#print axioms realPairPolarMatrix_power_energy
end SpectralRadiusUpperTail
