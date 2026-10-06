import SpectralRadiusUpperTail.RealSchurComplexEigenpairExistence
import SpectralRadiusUpperTail.RealSchurInvariantLineSpan
import SpectralRadiusUpperTail.RealSchurInvariantPlaneSpan
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Every nonempty real matrix has an invariant real subspace of
dimension one or two. This is the first induction step toward global
real Schur coverage; orthogonal extension and recursive reduction are
not included in this statement. -/
theorem realMatrix_exists_invariant_subspace_rank_one_or_two
    {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ P : Submodule ℝ (Fin n → ℝ),
      (Module.finrank ℝ P = 1 ∨ Module.finrank ℝ P = 2) ∧
      ∀ w ∈ P, A.mulVec w ∈ P := by
  obtain ⟨ζ,z,hz0,hz⟩ := realMatrix_exists_complex_eigenpair hn A
  by_cases hIm : ζ.im = 0
  · obtain ⟨u,hu,hAu⟩ :=
      realMatrix_realComplexEigenvalue_hasRealEigenvector A z ζ hz hz0 hIm
    obtain ⟨P,hP,hPinv⟩ := realMatrix_realEigenvector_invariant_line A ζ.re u hu hAu
    exact ⟨P,Or.inl hP,hPinv⟩
  · obtain ⟨P,hP,hPinv⟩ :=
      realMatrix_nonrealEigenpair_invariant_plane A z ζ hz hz0 hIm
    exact ⟨P,Or.inr hP,hPinv⟩

#print axioms realMatrix_exists_invariant_subspace_rank_one_or_two
end SpectralRadiusUpperTail
