import SpectralRadiusUpperTail.MarkedRealTwoBlockRegular
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Every simple real eigenline has a regular local two-block Schur
coordinate center, with the marked unit vector as its first basis vector. -/
theorem exists_markedRealEigenline_regular_center
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ) (hm : 0 < m)
    (hdim : Module.finrank ℝ E = m+1)
    (f : E →ₗ[ℝ] E) (hsep : f.charpoly.Separable)
    (v : E) (hv : ‖v‖ = 1)
    (x : ℝ) (hfv : f v = x • v) :
    ∃ b : OrthonormalBasis (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ E,
      b (markedRealFirstCoordinate m) = v ∧
      let T := LinearMap.toMatrix b.toBasis b.toBasis f
      realSchurMixedLowerProjection (markedRealTwoBlockSizes m) T = 0 ∧
        (realSchurMixedOrbitMatrix (markedRealTwoBlockSizes m) T).det ≠ 0 := by
  obtain ⟨b,hb,hT⟩ :=
    exists_markedRealEigenline_blockUpper m hdim f v hv x hfv
  refine ⟨b,hb,hT,?_⟩
  have hchar :
      (LinearMap.toMatrix b.toBasis b.toBasis f).charpoly = f.charpoly :=
    f.charpoly_toMatrix b.toBasis
  have hsepT :
      (LinearMap.toMatrix b.toBasis b.toBasis f).charpoly.Separable := by
    rw [hchar]
    exact hsep
  exact markedRealTwoBlock_orbit_det_ne_zero m hm _ hT hsepT

#print axioms exists_markedRealEigenline_regular_center
end SpectralRadiusUpperTail
