import SpectralRadiusUpperTail.MarkedRealStereoEigenvectorCoverage
import SpectralRadiusUpperTail.MarkedRealEigenlineRoot

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- A real root is covered whenever its eigenvectors avoid the equator.
The eigenvector sign is fixed inside the proof. -/
theorem markedRealStereo_realRoot_coverage (m : ℕ)
    (A : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hcoord : ∀ v : RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ,
      v ≠ 0 → ∀ z : ℝ, A *ᵥ v = z • v → v (markedRealFirstCoordinate m) ≠ 0)
    (z : ℝ) (hz : A.charpoly.IsRoot z) :
    ∃ p : RealSchurMixedTangent (markedRealTwoBlockSizes m),
      p.1 ∈ markedRealStereoSource m ∧ markedRealScalar m p.2.val = z ∧
        markedRealStereoMatrixMap m p = A := by
  have hchar : A.toEuclideanLin.charpoly = A.charpoly := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.charpoly_toLin A
      (EuclideanSpace.basisFun (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ).toBasis
  obtain ⟨v,hv,hAv⟩ := exists_unit_real_eigenvector_of_charpoly_root
    A.toEuclideanLin z (by rwa [hchar])
  let u : RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ := WithLp.ofLp v
  have hu : ∑ i, (u i)^2 = 1 := by
    change (∑ i, (v i)^2) = 1
    rw [← EuclideanSpace.real_norm_sq_eq, hv]
    norm_num
  have hAu : A *ᵥ u = z • u := by
    exact congrArg WithLp.ofLp hAv
  have hu0 : u ≠ 0 := by
    intro hzero
    simp [hzero] at hu
  have hnonzero := hcoord u hu0 z hAu
  rcases lt_or_gt_of_ne hnonzero with hneg | hpos
  · apply markedRealStereo_positive_unit_eigenvector_coverage m A (-u)
      (by simpa only [Pi.neg_apply, neg_sq] using hu) (by simpa using neg_pos.mpr hneg) z
    rw [Matrix.mulVec_neg, hAu, smul_neg]
  · exact markedRealStereo_positive_unit_eigenvector_coverage m A u hu hpos z hAu

#print axioms markedRealStereo_realRoot_coverage
end SpectralRadiusUpperTail
