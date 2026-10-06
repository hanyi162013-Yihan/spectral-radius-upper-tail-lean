import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Rows record a fixed coordinate of successive matrix powers. -/
def realMatrixObservation (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (A^i.val) k j

theorem realMatrix_power_mulVec_eigenvector (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (z : ℝ)
    (hv : A *ᵥ v = z • v) (l : ℕ) :
    (A^l) *ᵥ v = z^l • v := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv,
      smul_smul, pow_succ]

/-- A nonsingular observation matrix excludes every eigenvector whose
chosen coordinate vanishes, simultaneously for all real eigenvalues. -/
theorem realMatrix_eigenvector_coordinate_ne_zero (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n)
    (hdet : (realMatrixObservation n A k).det ≠ 0)
    (v : Fin n → ℝ) (hv0 : v ≠ 0) (z : ℝ) (hv : A *ᵥ v = z • v) :
    v k ≠ 0 := by
  intro hk
  apply hv0
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  funext i
  change ((A^i.val) *ᵥ v) k = 0
  rw [realMatrix_power_mulVec_eigenvector n A v z hv i.val]
  simp [hk]

#print axioms realMatrix_power_mulVec_eigenvector
#print axioms realMatrix_eigenvector_coordinate_ne_zero
end SpectralRadiusUpperTail
