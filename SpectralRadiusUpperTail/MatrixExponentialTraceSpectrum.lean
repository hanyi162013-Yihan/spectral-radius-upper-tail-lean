import SpectralRadiusUpperTail.MatrixWeightedTrace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

namespace SpectralRadiusUpperTail
open scoped ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Real trace of a Hermitian functional calculus, computed by diagonalization. -/
lemma matrix_real_trace_cfc {A : Matrix ι ι 𝕂} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    RCLike.re (cfc f A).trace = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal,
    map_sum, Function.comp_apply, RCLike.ofReal_re]

/-- The exponential trace is the sum of exponentials of the actual eigenvalues. -/
lemma matrix_real_trace_exp {A : Matrix ι ι 𝕂} (hA : A.IsHermitian) :
    RCLike.re (NormedSpace.exp A).trace = ∑ i, Real.exp (hA.eigenvalues i) := by
  rw [← CFC.real_exp_eq_normedSpace_exp (show IsSelfAdjoint A from hA)]
  exact matrix_real_trace_cfc hA Real.exp

/-- Any one eigenvalue supplies a lower bound on the exponential trace. -/
lemma matrix_exp_eigenvalue_le_trace {A : Matrix ι ι 𝕂} (hA : A.IsHermitian) (i : ι) :
    Real.exp (hA.eigenvalues i) ≤ RCLike.re (NormedSpace.exp A).trace := by
  rw [matrix_real_trace_exp hA]
  exact Finset.single_le_sum (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

lemma matrix_exp_threshold_le_trace {A : Matrix ι ι 𝕂} (hA : A.IsHermitian)
    {t : ℝ} (h : ∃ i, t ≤ hA.eigenvalues i) :
    Real.exp t ≤ RCLike.re (NormedSpace.exp A).trace := by
  obtain ⟨i, hi⟩ := h
  exact (Real.exp_le_exp.mpr hi).trans (matrix_exp_eigenvalue_le_trace hA i)

#print axioms matrix_real_trace_cfc
#print axioms matrix_exp_threshold_le_trace
end SpectralRadiusUpperTail
