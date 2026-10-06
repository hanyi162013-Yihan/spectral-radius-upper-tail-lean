import SpectralRadiusUpperTail.MatrixCoefficient
import SpectralRadiusUpperTail.ResolventFiniteExpansion
import Mathlib.LinearAlgebra.Eigenspace.Matrix

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix
variable {n : ℕ}

lemma rankOne_mulVec (v w : Fin n → ℂ) (b : ℂ) :
    (b • Matrix.vecMulVec v (star v)).mulVec w =
      (b*(∑ i, star (v i)*w i)) • v := by
  ext i
  simp only [Matrix.mulVec,dotProduct,Matrix.smul_apply,Matrix.vecMulVec_apply,
    Pi.smul_apply,smul_eq_mul,Pi.star_apply,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma resolvent_mulVec_equation (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (z : ℂ) (hz : z ∈ resolventSet ℂ A) :
    z • (resolvent A z).mulVec v-A.mulVec ((resolvent A z).mulVec v) = v := by
  have hi : (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) z-A)*resolvent A z = 1 :=
    Ring.mul_inverse_cancel _ (spectrum.mem_resolventSet_iff.mp hz)
  have hh := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ => B.mulVec v) hi
  rw [← Matrix.mulVec_mulVec,Matrix.sub_mulVec,Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mulVec,Matrix.one_mulVec,Matrix.one_mulVec] at hh
  exact hh

/-- A zero of the scalar rank-one equation gives an actual nonzero eigenvector. -/
lemma rankOne_resolvent_eigenvector (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (b z : ℂ) (hz : z ∈ resolventSet ℂ A) (h : b*matrixCoefficient v v (resolvent A z) = 1) :
    (resolvent A z).mulVec v ≠ 0 ∧
      (A+b • Matrix.vecMulVec v (star v)).mulVec ((resolvent A z).mulVec v) =
        z • ((resolvent A z).mulVec v) := by
  let w := (resolvent A z).mulVec v
  have hc : b*(∑ i, star (v i)*w i) = 1 := by
    simpa only [matrixCoefficient_eq_sum] using h
  have hw : w ≠ 0 := by
    intro hh
    rw [hh] at hc
    simp at hc
  refine ⟨hw,?_⟩
  change (A+b • Matrix.vecMulVec v (star v)).mulVec w = z • w
  rw [Matrix.add_mulVec,rankOne_mulVec,hc,one_smul]
  have he := resolvent_mulVec_equation A v z hz
  change z • w-A.mulVec w = v at he
  rw [← he]
  abel

lemma rankOne_resolvent_mem_spectrum (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (b z : ℂ) (hz : z ∈ resolventSet ℂ A) (h : b*matrixCoefficient v v (resolvent A z) = 1) :
    z ∈ spectrum ℂ (A+b • Matrix.vecMulVec v (star v)) := by
  have hh := rankOne_resolvent_eigenvector A v b z hz h
  have hv : Module.End.HasEigenvector (A+b • Matrix.vecMulVec v (star v)).toLin' z
      ((resolvent A z).mulVec v) := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_,hh.1⟩
    exact hh.2
  have he := (Module.End.hasEigenvalue_of_hasEigenvector hv).mem_spectrum
  rw [Matrix.spectrum_toLin'] at he
  exact he

#print axioms rankOne_mulVec
#print axioms resolvent_mulVec_equation
#print axioms rankOne_resolvent_eigenvector
#print axioms rankOne_resolvent_mem_spectrum
end SpectralRadiusUpperTail
