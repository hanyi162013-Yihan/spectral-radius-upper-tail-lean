import SpectralRadiusUpperTail.MarkedRealStereoRootCoverage
import SpectralRadiusUpperTail.MarkedRealStereoRankArea
import SpectralRadiusUpperTail.RealEigenvectorCoordinateReindex

namespace SpectralRadiusUpperTail
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator

theorem markedRealStereoRank_image_has_rankedRoot (m k : ℕ) (hm : 0 < m) (b : ℝ)
    (y : RealSchurMixedTangent (markedRealTwoBlockSizes m))
    (hy : y ∈ markedRealStereoEntryMap m ''
      (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b)) :
    let A := (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y
    A.charpoly.Separable ∧ ∃ z : ℝ, A.charpoly.IsRoot z ∧ b < z ∧
      realPolynomialRootRank A.charpoly z = k := by
  rcases hy with ⟨p,hp,hpy⟩
  let A := (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y
  have hA : A = markedRealStereoMatrixMap m p := by
    have hh := congrArg (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm hpy
    simpa only [markedRealStereoEntryMap, LinearEquiv.symm_apply_apply] using hh.symm
  have hpoly : A.charpoly = p.2.val.charpoly := by
    rw [hA, markedRealStereoMatrixMap]
    exact realMatrixOrthogonalConjugation_charpoly _ _ _
      (markedRealStereoNativeFrame_orthogonal m p.1)
  change A.charpoly.Separable ∧ ∃ z : ℝ, A.charpoly.IsRoot z ∧ b < z ∧
    realPolynomialRootRank A.charpoly z = k
  rw [hpoly]
  exact ⟨hp.2.1, markedRealScalar m p.2.val, markedRealUpper_scalar_isRoot m hm p.2,
    hp.2.2.1, hp.2.2.2⟩

theorem markedRealStereoRank_mem_image_of_root (m : ℕ) (b z : ℝ)
    (y : RealSchurMixedTangent (markedRealTwoBlockSizes m))
    (hcoord : realMatrixEigenvectorsHaveNonzeroCoordinates
      (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y))
    (hsep : ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y).charpoly.Separable)
    (hz : ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y).charpoly.IsRoot z)
    (hb : b < z) :
    y ∈ markedRealStereoEntryMap m ''
      (markedRealStereoSource m ×ˢ markedRealUpperRankSource m
        (realPolynomialRootRank
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y).charpoly z) b) := by
  let A := (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y
  obtain ⟨p,hp,hscalar,hpA⟩ := markedRealStereo_realRoot_coverage m A
    (fun v hv x hx => hcoord v hv x hx (markedRealFirstCoordinate m)) z hz
  have hpoly : p.2.val.charpoly = A.charpoly := by
    rw [← hpA, markedRealStereoMatrixMap,
      realMatrixOrthogonalConjugation_charpoly _ _ _
        (markedRealStereoNativeFrame_orthogonal m p.1)]
  refine ⟨p, ⟨hp, ?_⟩, ?_⟩
  · change p.2.val.charpoly.Separable ∧ b < markedRealScalar m p.2.val ∧
      realPolynomialRootRank p.2.val.charpoly (markedRealScalar m p.2.val) = _
    rw [hpoly, hscalar]
    exact ⟨hsep,hb,rfl⟩
  · change realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)
      (markedRealStereoMatrixMap m p) = y
    rw [hpA]
    exact LinearEquiv.apply_symm_apply _ _

theorem measurableSet_markedRealStereoRankImage (m k : ℕ) (hm : 0 < m) (b : ℝ) :
    MeasurableSet (markedRealStereoEntryMap m ''
      (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b)) := by
  exact measurable_image_of_fderivWithin (measurableSet_markedRealStereoRankProduct m k b)
    (fun x _ => (markedRealStereoEntryMap_differentiable m x).hasFDerivAt.hasFDerivWithinAt)
    (markedRealStereoEntryMap_injOn_rank m k hm b)

#print axioms markedRealStereoRank_image_has_rankedRoot
#print axioms markedRealStereoRank_mem_image_of_root
#print axioms measurableSet_markedRealStereoRankImage
end SpectralRadiusUpperTail
