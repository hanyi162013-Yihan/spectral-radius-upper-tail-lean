import SpectralRadiusUpperTail.RealFiniteComplexEigenplane
import SpectralRadiusUpperTail.RealInvariantPairRestriction
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

namespace SpectralRadiusUpperTail
open scoped Matrix

theorem realMatrix_nonrealEigenpair_euclidean_plane
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (z : ι → ℂ) (ζ : ℂ)
    (hz : (A.map Complex.ofRealHom).mulVec z=ζ • z)
    (hz0 : z ≠ 0) (hIm : ζ.im ≠ 0) :
    ∃ P : Submodule ℝ (EuclideanSpace ℝ ι), Module.finrank ℝ P=2 ∧
      ∃ hInv : ∀ x ∈ P, A.toEuclideanLin x ∈ P,
        (A.toEuclideanLin.restrict hInv).charpoly =
          Polynomial.X^2-Polynomial.C (2*ζ.re)*Polynomial.X+
            Polynomial.C (ζ.re^2+ζ.im^2) := by
  let e := (EuclideanSpace.equiv ι ℝ).symm
  let u := e (fun i => (z i).re)
  let v := e (fun i => (z i).im)
  have hLI : LinearIndependent ℝ ![u,v] := by
    have h := (realMatrix_nonrealEigenvector_re_im_independent_finite A z ζ hz hz0 hIm).map_injOn
      e.toLinearMap e.injective.injOn
    have he : e.toLinearMap ∘ ![(fun i => (z i).re),(fun i => (z i).im)] = ![u,v] := by
      funext i
      fin_cases i <;> rfl
    rw [he] at h
    exact h
  have hpair := realMatrix_complexEigenvector_re_im_finite A z ζ hz
  have hu : A.toEuclideanLin u=ζ.re • u-ζ.im • v := by
    change e (A.mulVec (fun i => (z i).re))=_
    rw [hpair.1,map_sub,map_smul,map_smul]
  have hv : A.toEuclideanLin v=ζ.im • u+ζ.re • v := by
    change e (A.mulVec (fun i => (z i).im))=_
    rw [hpair.2,map_add,map_smul,map_smul]
  obtain ⟨hInv,hpoly⟩ := realInvariantPair_restrict_charpoly A.toEuclideanLin
    u v ζ.re ζ.im hLI hu hv
  refine ⟨Submodule.span ℝ (Set.range ![u,v]),?_,hInv,hpoly⟩
  simpa using finrank_span_eq_card hLI

theorem realMatrix_nonrealRoot_euclidean_plane
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (ζ : ℂ)
    (hroot : (A.charpoly.map Complex.ofRealHom).IsRoot ζ)
    (hIm : ζ.im ≠ 0) :
    ∃ P : Submodule ℝ (EuclideanSpace ℝ ι), Module.finrank ℝ P=2 ∧
      ∃ hInv : ∀ x ∈ P, A.toEuclideanLin x ∈ P,
        (A.toEuclideanLin.restrict hInv).charpoly =
          Polynomial.X^2-Polynomial.C (2*ζ.re)*Polynomial.X+
            Polynomial.C (ζ.re^2+ζ.im^2) := by
  let f := (A.map Complex.ofRealHom).mulVecLin
  have hf : f.charpoly.IsRoot ζ := by
    simpa only [f,Matrix.charpoly_mulVecLin,Matrix.charpoly_map] using hroot
  obtain ⟨z,hz⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly f ζ).mpr hf).exists_hasEigenvector
  exact realMatrix_nonrealEigenpair_euclidean_plane A z ζ hz.apply_eq_smul hz.2 hIm

#print axioms realMatrix_nonrealEigenpair_euclidean_plane
#print axioms realMatrix_nonrealRoot_euclidean_plane
end SpectralRadiusUpperTail
