import SpectralRadiusUpperTail.RealSchurComplexEigenplane
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Every nonempty finite real matrix has a nonzero complex eigenvector.
This supplies the algebraically closed starting point for the real
one-dimensional/two-dimensional Schur induction. -/
theorem realMatrix_exists_complex_eigenpair
    {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (ζ : ℂ) (z : Fin n → ℂ), z ≠ 0 ∧
      (A.map Complex.ofRealHom).mulVec z = ζ • z := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let f : Module.End ℂ (Fin n → ℂ) :=
    Matrix.mulVecLin (A.map Complex.ofRealHom)
  obtain ⟨ζ,hζ⟩ := Module.End.exists_eigenvalue f
  obtain ⟨z,hz⟩ := hζ.exists_hasEigenvector
  refine ⟨ζ,z,hz.2,?_⟩
  simpa only [f, Matrix.mulVecLin_apply] using hz.apply_eq_smul

#print axioms realMatrix_exists_complex_eigenpair
end SpectralRadiusUpperTail
