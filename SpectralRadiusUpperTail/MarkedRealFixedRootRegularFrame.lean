import SpectralRadiusUpperTail.MarkedRealRootRegularFrame
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The preceding marked-root regular frame is available for an actual
fixed-size matrix after a fixed permutation of entry coordinates. -/
theorem exists_fixedRealRoot_regular_frame
    (m : ℕ) (hm : 0 < m)
    (A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (hsep : A.charpoly.Separable)
    (x : ℝ) (hx : A.charpoly.IsRoot x) :
    ∃ e : Fin (m+1) ≃ RealSchurMixedCoord (markedRealTwoBlockSizes m),
      ∃ c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m),
        markedRealScalar m c.T = x ∧
          Matrix.reindex e e A = c.Q * c.T * c.Qᵀ := by
  have hcard : Fintype.card (Fin (m+1)) =
      Fintype.card (RealSchurMixedCoord (markedRealTwoBlockSizes m)) := by
    rw [Fintype.card_fin, markedRealTwoBlock_card]
  let e : Fin (m+1) ≃ RealSchurMixedCoord (markedRealTwoBlockSizes m) :=
    Fintype.equivOfCardEq hcard
  have hchar : (Matrix.reindex e e A).charpoly = A.charpoly :=
    Matrix.charpoly_reindex e A
  have hsep' : (Matrix.reindex e e A).charpoly.Separable := by
    rw [hchar]
    exact hsep
  have hx' : (Matrix.reindex e e A).charpoly.IsRoot x := by
    rw [hchar]
    exact hx
  obtain ⟨c,hxcoord,hA⟩ :=
    exists_markedRealRoot_regular_frame m hm (Matrix.reindex e e A) hsep' x hx'
  exact ⟨e,c,hxcoord,hA⟩

#print axioms exists_fixedRealRoot_regular_frame
end SpectralRadiusUpperTail
