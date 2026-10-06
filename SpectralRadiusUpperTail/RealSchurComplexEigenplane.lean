import SpectralRadiusUpperTail.ComplexVectorEnergy
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A complex eigenvector of a real matrix gives two real vectors on
which the matrix acts by the real 2×2 block of its eigenvalue. -/
theorem realMatrix_complexEigenvector_re_im
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℂ) (ζ : ℂ)
    (hz : (A.map Complex.ofRealHom).mulVec z = ζ • z) :
    A.mulVec (fun i => (z i).re) =
        ζ.re • (fun i => (z i).re) - ζ.im • (fun i => (z i).im) ∧
      A.mulVec (fun i => (z i).im) =
        ζ.im • (fun i => (z i).re) + ζ.re • (fun i => (z i).im) := by
  constructor
  · funext i
    have hi := congrArg Complex.re (congrFun hz i)
    calc
      (A.mulVec (fun j => (z j).re)) i =
          (((A.map Complex.ofRealHom).mulVec z) i).re :=
        congrFun (real_matrix_complex_mulVec_re A z).symm i
      _ = (ζ * z i).re := by simpa [Pi.smul_apply, smul_eq_mul] using hi
      _ = (ζ.re • (fun j => (z j).re) -
          ζ.im • (fun j => (z j).im)) i := by
        simp [Complex.mul_re, Pi.smul_apply, smul_eq_mul]
  · funext i
    have hi := congrArg Complex.im (congrFun hz i)
    calc
      (A.mulVec (fun j => (z j).im)) i =
          (((A.map Complex.ofRealHom).mulVec z) i).im :=
        congrFun (real_matrix_complex_mulVec_im A z).symm i
      _ = (ζ * z i).im := by simpa [Pi.smul_apply, smul_eq_mul] using hi
      _ = (ζ.im • (fun j => (z j).re) +
          ζ.re • (fun j => (z j).im)) i := by
        simp [Complex.mul_im, Pi.smul_apply, smul_eq_mul]
        ring

#print axioms realMatrix_complexEigenvector_re_im
end SpectralRadiusUpperTail
