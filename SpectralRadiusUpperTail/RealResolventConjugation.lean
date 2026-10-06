import SpectralRadiusUpperTail.RingEquivInverse
import SpectralRadiusUpperTail.MatrixCoefficient
import Mathlib.Analysis.Normed.Algebra.Spectrum

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix
variable {n : ℕ}

lemma real_matrix_resolvent_conjugate (A : Matrix (Fin n) (Fin n) ℝ) (z : ℂ) :
    resolvent (A.map Complex.ofRealHom) (star z) =
      (resolvent (A.map Complex.ofRealHom) z).map (starRingAut (R := ℂ)) := by
  let F : Matrix (Fin n) (Fin n) ℂ ≃+* Matrix (Fin n) (Fin n) ℂ :=
    (starRingAut (R := ℂ)).mapMatrix
  have he : F (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) z-A.map Complex.ofRealHom) =
      algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (star z)-A.map Complex.ofRealHom := by
    ext i j
    simp [F,Algebra.algebraMap_eq_smul_one,Matrix.smul_apply,Matrix.one_apply,
      Matrix.sub_apply,apply_ite]
  have hh := ringEquiv_map_ringInverse F
    (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) z-A.map Complex.ofRealHom)
  rw [he] at hh
  exact hh.symm

lemma real_matrixCoefficient_conjugate (v : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    matrixCoefficient (fun i => (v i : ℂ)) (fun i => (v i : ℂ)) (A.map (starRingAut (R := ℂ))) =
      star (matrixCoefficient (fun i => (v i : ℂ)) (fun i => (v i : ℂ)) A) := by
  simp only [matrixCoefficient_eq_sum,Matrix.mulVec,dotProduct]
  simp [map_sum,map_mul,star_sum,star_mul,mul_comm]

lemma real_resolvent_fixedPoint_conjugate (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (b : ℝ) (z : ℂ) :
    (b : ℂ)*(star z)*matrixCoefficient (fun i => (v i : ℂ)) (fun i => (v i : ℂ))
      (resolvent (A.map Complex.ofRealHom) (star z)) =
    star ((b : ℂ)*z*matrixCoefficient (fun i => (v i : ℂ)) (fun i => (v i : ℂ))
      (resolvent (A.map Complex.ofRealHom) z)) := by
  rw [real_matrix_resolvent_conjugate,real_matrixCoefficient_conjugate]
  simp [star_mul,mul_comm]

#print axioms real_matrix_resolvent_conjugate
#print axioms real_matrixCoefficient_conjugate
#print axioms real_resolvent_fixedPoint_conjugate
end SpectralRadiusUpperTail
