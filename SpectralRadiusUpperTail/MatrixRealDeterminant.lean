import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex

namespace SpectralRadiusUpperTail
open scoped ComplexOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

lemma determinant_toEuclideanCLM (A : Matrix (Fin n) (Fin n) 𝕂) :
    LinearMap.det (Matrix.toEuclideanCLM (𝕜 := 𝕂) (n := Fin n) A).toLinearMap = A.det := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin]

lemma complex_real_determinant (A : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A).toLinearMap.restrictScalars ℝ) = ‖A.det‖^2 := by
  rw [LinearMap.det_restrictScalars,determinant_toEuclideanCLM,Algebra.norm_complex_eq]
  exact Complex.normSq_eq_norm_sq _

#print axioms determinant_toEuclideanCLM
#print axioms complex_real_determinant
end SpectralRadiusUpperTail
