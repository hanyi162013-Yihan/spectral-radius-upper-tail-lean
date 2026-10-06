import SpectralRadiusUpperTail.MarkedNonrealAdaptedBasis
import SpectralRadiusUpperTail.RealSchurArbitraryBlockRegular
import SpectralRadiusUpperTail.RealSchurOrthonormalConjugation
import SpectralRadiusUpperTail.RealSchurMixedRegularAtlas

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A prescribed invariant plane of a simple-spectrum matrix gives a
regular marked-pair frame with its exact restricted polynomial. -/
theorem exists_markedNonreal_regular_frame
    (m : ℕ) (hm : 0 < m)
    (A : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ)
    (hsep : A.charpoly.Separable)
    (P : Submodule ℝ (EuclideanSpace ℝ (RealSchurMixedCoord (markedNonrealBlockSizes m))))
    (hP : Module.finrank ℝ P=2)
    (hInv : ∀ x ∈ P, A.toEuclideanLin x ∈ P) :
    ∃ c : RealSchurMixedRegularFrame (markedNonrealBlockSizes m),
      (markedNonrealFirstBlock m c.T).charpoly = (A.toEuclideanLin.restrict hInv).charpoly ∧
      A=c.Q*c.T*c.Qᵀ := by
  let ι := RealSchurMixedCoord (markedNonrealBlockSizes m)
  let f := A.toEuclideanLin
  have hchar : f.charpoly=A.charpoly := by
    dsimp [f]
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.charpoly_toLin A (EuclideanSpace.basisFun ι ℝ).toBasis
  obtain ⟨b,hT,hblock⟩ := exists_markedNonreal_adapted_basis m
    (by rw [finrank_euclideanSpace,markedNonrealCoord_card]) f P hP hInv
  let T := LinearMap.toMatrix b.toBasis b.toBasis f
  have hreg : (realSchurMixedOrbitMatrix (markedNonrealBlockSizes m) T).det ≠ 0 := by
    apply realSchurMixed_simpleSpectrum_orbit_regular_general _
      (markedNonrealBlockSizes_pos m hm) T hT
    rw [f.charpoly_toMatrix,hchar]
    exact hsep
  let u := EuclideanSpace.basisFun ι ℝ
  let Q := u.toBasis.toMatrix b
  obtain ⟨hQ,hconj⟩ := realOrthonormalBasis_matrix_conjugation u b f
  have hstd : LinearMap.toMatrix u.toBasis u.toBasis f=A := by
    change LinearMap.toMatrix u.toBasis u.toBasis
      (Matrix.toLin u.toBasis u.toBasis A)=A
    exact LinearMap.toMatrix_toLin u.toBasis u.toBasis A
  refine ⟨⟨T,hT,hreg,Q,hQ⟩,hblock,?_⟩
  change A=Q*T*Qᵀ
  rw [← hstd]
  exact hconj

#print axioms exists_markedNonreal_regular_frame
end SpectralRadiusUpperTail
