import SpectralRadiusUpperTail.MatrixUnitaryFrobenius
import SpectralRadiusUpperTail.MatrixRadiusEigenvalue
import SpectralRadiusUpperTail.SpectralWitness
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius

/-- Orthogonal or unitary similarity leaves the characteristic polynomial
unchanged, including every root multiplicity. -/
theorem matrix_unitary_conjugation_charpoly
    {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕂)
    (U : Matrix.unitaryGroup (Fin n) 𝕂) :
    ((U : Matrix (Fin n) (Fin n) 𝕂) * A *
      (U : Matrix (Fin n) (Fin n) 𝕂)ᴴ).charpoly = A.charpoly := by
  let u : Matrix (Fin n) (Fin n) 𝕂 := U
  have hu : uᴴ * u = 1 := by
    simpa [u, Matrix.star_eq_conjTranspose] using
      (Unitary.coe_star_mul_self U)
  change (u*A*uᴴ).charpoly = A.charpoly
  rw [Matrix.charpoly_mul_comm (u*A) uᴴ]
  rw [← Matrix.mul_assoc, hu, Matrix.one_mul]

theorem matrix_unitary_conjugation_spectralRadius
    {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕂)
    (U : Matrix.unitaryGroup (Fin n) 𝕂) :
    spectralRadius 𝕂
      ((U : Matrix (Fin n) (Fin n) 𝕂) * A *
        (U : Matrix (Fin n) (Fin n) 𝕂)ᴴ) =
      spectralRadius 𝕂 A := by
  have hpoly := matrix_unitary_conjugation_charpoly A U
  have hs : spectrum 𝕂
      ((U : Matrix (Fin n) (Fin n) 𝕂) * A *
        (U : Matrix (Fin n) (Fin n) 𝕂)ᴴ) = spectrum 𝕂 A := by
    ext z
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
      Matrix.mem_spectrum_iff_isRoot_charpoly, hpoly]
  simp only [spectralRadius, hs]

/-- For real matrices this preserves the ordinary radius of all complex
eigenvalues, including nonreal conjugate pairs. -/
theorem realMatrixRadius_orthogonal_conjugation
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℝ) :
    realMatrixRadius
      ((U : Matrix (Fin n) (Fin n) ℝ) * A *
        (U : Matrix (Fin n) (Fin n) ℝ)ᴴ) =
      realMatrixRadius A := by
  have hreal := matrix_unitary_conjugation_charpoly A U
  have hcomplex :
      (((U : Matrix (Fin n) (Fin n) ℝ) * A *
        (U : Matrix (Fin n) (Fin n) ℝ)ᴴ).map Complex.ofRealHom).charpoly =
        (A.map Complex.ofRealHom).charpoly := by
    rw [Matrix.charpoly_map, Matrix.charpoly_map, hreal]
  have hs : spectrum ℂ
      (((U : Matrix (Fin n) (Fin n) ℝ) * A *
        (U : Matrix (Fin n) (Fin n) ℝ)ᴴ).map Complex.ofRealHom) =
      spectrum ℂ (A.map Complex.ofRealHom) := by
    ext z
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
      Matrix.mem_spectrum_iff_isRoot_charpoly, hcomplex]
  simp only [realMatrixRadius, spectralRadius, hs]

#print axioms matrix_unitary_conjugation_charpoly
#print axioms matrix_unitary_conjugation_spectralRadius
#print axioms realMatrixRadius_orthogonal_conjugation
end SpectralRadiusUpperTail
