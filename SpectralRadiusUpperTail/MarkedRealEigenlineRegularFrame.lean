import SpectralRadiusUpperTail.MarkedRealEigenlineRegularCenter
import SpectralRadiusUpperTail.RealSchurOrthonormalConjugation
import SpectralRadiusUpperTail.RealSchurMixedRegularAtlas
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A simple real eigenline of a matrix in mixed scalar coordinates yields
a regular orthogonal-conjugation frame for the actual matrix. -/
theorem exists_markedRealEigenline_regular_frame
    (m : ℕ) (hm : 0 < m)
    (A : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hsep : A.charpoly.Separable)
    (v : EuclideanSpace ℝ (RealSchurMixedCoord (markedRealTwoBlockSizes m)))
    (hv : ‖v‖ = 1) (x : ℝ)
    (hAv : A.toEuclideanLin v = x • v) :
    ∃ b : OrthonormalBasis
        (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ
        (EuclideanSpace ℝ (RealSchurMixedCoord (markedRealTwoBlockSizes m))),
      ∃ c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m),
        b (markedRealFirstCoordinate m) = v ∧
          c.T = LinearMap.toMatrix b.toBasis b.toBasis A.toEuclideanLin ∧
          A = c.Q * c.T * c.Qᵀ := by
  let ι := RealSchurMixedCoord (markedRealTwoBlockSizes m)
  let f := A.toEuclideanLin
  have hchar : f.charpoly = A.charpoly := by
    dsimp [f]
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.charpoly_toLin A (EuclideanSpace.basisFun ι ℝ).toBasis
  obtain ⟨b,hb,hT,hdet⟩ :=
    exists_markedRealEigenline_regular_center m hm
      (by rw [finrank_euclideanSpace, markedRealTwoBlock_card])
      f (by rw [hchar]; exact hsep) v hv x hAv
  let u : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι) :=
    EuclideanSpace.basisFun ι ℝ
  let Q := u.toBasis.toMatrix b
  let T := LinearMap.toMatrix b.toBasis b.toBasis f
  obtain ⟨hQ,hconj⟩ :=
    realOrthonormalBasis_matrix_conjugation u b f
  have hstd : LinearMap.toMatrix u.toBasis u.toBasis f = A := by
    change LinearMap.toMatrix u.toBasis u.toBasis
      (Matrix.toLin u.toBasis u.toBasis A) = A
    exact LinearMap.toMatrix_toLin u.toBasis u.toBasis A
  let c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m) :=
    ⟨T,hT,hdet,Q,hQ⟩
  refine ⟨b,c,hb,rfl,?_⟩
  change A = Q*T*Qᵀ
  rw [← hstd]
  exact hconj

#print axioms exists_markedRealEigenline_regular_frame
end SpectralRadiusUpperTail
