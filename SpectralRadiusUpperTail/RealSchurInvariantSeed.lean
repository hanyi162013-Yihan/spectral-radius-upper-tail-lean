import SpectralRadiusUpperTail.RealSchurComplexEigenpairExistence
import SpectralRadiusUpperTail.RealSchurComplexEigenline
import SpectralRadiusUpperTail.RealSchurComplexEigenplaneIndependent
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The first algebraic step of real Schur reduction: a nonempty real
matrix has either a real eigenline or a genuinely two-dimensional
invariant plane carrying a nonreal conjugate eigenvalue pair. -/
theorem realMatrix_exists_invariant_line_or_plane
    {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃ (a : ℝ) (u : Fin n → ℝ), u ≠ 0 ∧ A.mulVec u = a • u) ∨
    (∃ (a b : ℝ) (u v : Fin n → ℝ), b ≠ 0 ∧
      LinearIndependent ℝ ![u,v] ∧
      A.mulVec u = a • u - b • v ∧
      A.mulVec v = b • u + a • v) := by
  obtain ⟨ζ,z,hz0,hz⟩ := realMatrix_exists_complex_eigenpair hn A
  by_cases hIm : ζ.im = 0
  · left
    obtain ⟨u,hu,hAu⟩ :=
      realMatrix_realComplexEigenvalue_hasRealEigenvector A z ζ hz hz0 hIm
    exact ⟨ζ.re,u,hu,hAu⟩
  · right
    refine ⟨ζ.re,ζ.im,(fun i => (z i).re),(fun i => (z i).im),hIm,?_,?_⟩
    · exact realMatrix_nonrealEigenvector_re_im_independent A z ζ hz hz0 hIm
    · exact realMatrix_complexEigenvector_re_im A z ζ hz

#print axioms realMatrix_exists_invariant_line_or_plane
end SpectralRadiusUpperTail
