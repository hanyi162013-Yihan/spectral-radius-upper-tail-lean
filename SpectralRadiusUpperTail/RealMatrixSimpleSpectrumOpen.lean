import SpectralRadiusUpperTail.RealSchurMixedSimpleSpectrum
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Simple characteristic spectrum is an open condition on a finite real
matrix. This lets the marked-root chart sources be Borel sets. -/
theorem isOpen_realMatrix_charpoly_separable
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsOpen {A : Matrix ι ι ℝ | A.charpoly.Separable} := by
  let F : Matrix ι ι ℝ → ℝ := fun A =>
    MvPolynomial.eval (fun ij : ι × ι => A ij.1 ij.2)
      (finiteRealMatrixCollisionPolynomial ι)
  have hF : Continuous F := by
    unfold F
    exact (MvPolynomial.continuous_eval
      (finiteRealMatrixCollisionPolynomial ι)).comp (by fun_prop)
  have heq : {A : Matrix ι ι ℝ | A.charpoly.Separable} =
      F ⁻¹' ({(0 : ℝ)}ᶜ) := by
    ext A
    exact (finiteRealMatrixCollisionPolynomial_eval_ne_zero_iff ι
      (fun ij => A ij.1 ij.2)).symm
  rw [heq]
  exact (isOpen_compl_singleton : IsOpen ({(0 : ℝ)}ᶜ)).preimage hF

#print axioms isOpen_realMatrix_charpoly_separable
end SpectralRadiusUpperTail
