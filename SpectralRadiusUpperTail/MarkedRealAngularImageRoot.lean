import SpectralRadiusUpperTail.MarkedRealAngularGaussianMomentSimple
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Set
open scoped Matrix

/-- Every matrix counted by a fixed angular/rank image has a genuine
simple real eigenvalue above the cutoff. -/
theorem markedRealAngularRank_image_has_realRoot
    (m k : ℕ) (hm : 0 < m) (b : ℝ)
    (y : RealSchurMixedTangent (markedRealTwoBlockSizes m))
    (hy : y ∈
      realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 ''
        (markedRealAngularPositiveSource m ×ˢ
          markedRealUpperRankSource m k b)) :
    let A := (realSchurMixedEntryEquiv
      (markedRealTwoBlockSizes m)).symm y
    A.charpoly.Separable ∧
      ∃ x : ℝ, A.charpoly.IsRoot x ∧ b < x := by
  rcases hy with ⟨p,hp,hpy⟩
  let s := markedRealTwoBlockSizes m
  let A := (realSchurMixedEntryEquiv s).symm y
  have hA : A = (markedRealAngularProductMap m p).1 := by
    have h := congrArg (realSchurMixedEntryEquiv s).symm hpy
    simpa [A, s, markedRealAngularProductMap,
      realSchurMixedEntryCoordinates,
      realSchurMixedExpCoordinates_eq_conjugation,
      zero_add] using h.symm
  have hpoly : A.charpoly = p.2.val.charpoly := by
    rw [hA]
    exact realMatrixOrthogonalConjugation_charpoly _ _ _
      (realSchurMixedAngularFrame_orthogonal s p.1)
  change A.charpoly.Separable ∧
    ∃ x : ℝ, A.charpoly.IsRoot x ∧ b < x
  rw [hpoly]
  exact ⟨hp.2.1,
    ⟨markedRealScalar m p.2.val,
      markedRealUpper_scalar_isRoot m hm p.2, hp.2.2.1⟩⟩

#print axioms markedRealAngularRank_image_has_realRoot
end SpectralRadiusUpperTail
