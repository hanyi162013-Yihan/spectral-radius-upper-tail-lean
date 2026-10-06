import SpectralRadiusUpperTail.MarkedNonrealRootFrame
import SpectralRadiusUpperTail.RealSchurCanonicalSpectrumSimple
import SpectralRadiusUpperTail.RealSchurMixedCodeMultiplicity

namespace SpectralRadiusUpperTail

theorem markedNonreal_realized_code_exists
    (m : ℕ) (hm : 0 < m)
    (A : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ)
    (hA : A.charpoly.Separable)
    (i : Fin (Fintype.card (RealSchurMixedCoord (markedNonrealBlockSizes m))))
    (hi : (realSchurMixedCanonicalSpectrum (markedNonrealBlockSizes m) A i).im ≠ 0) :
    ∃ code : Fin 2 → Fin (Fintype.card (RealSchurMixedCoord (markedNonrealBlockSizes m))) → Bool,
      A ∈ realSchurMixedCodeClass (markedNonrealBlockSizes m) code ∧ code 0 i=true := by
  let s := markedNonrealBlockSizes m
  let z := realSchurMixedCanonicalSpectrum s A i
  have hz : (A.charpoly.map Complex.ofRealHom).IsRoot z :=
    realSchurMixedCanonicalSpectrum_isRoot s A hA i
  obtain ⟨c,hroot,hrep⟩ := exists_markedNonrealRoot_regular_frame m hm A hA z hz hi
  have hAT : A.charpoly=c.T.charpoly := by
    rw [hrep,realMatrixOrthogonalConjugation_charpoly _ _ _ c.orthogonal]
  have hTs : c.T.charpoly.Separable := hAT ▸ hA
  have hlabels := realSchurMixedCanonicalSpectrum_eq_of_charpoly s c.T A hTs hA hAT.symm
  refine ⟨realSchurMixedSpectralCode s c.T,?_,?_⟩
  · exact ⟨⟨c.Q,c.orthogonal⟩,c.T,c.upper,hTs,rfl,hrep⟩
  · change decide (((realSchurMixedDiagonalMatrix s c.T 0).charpoly.map Complex.ofRealHom).eval
      (realSchurMixedCanonicalSpectrum s c.T i)=0)=true
    rw [decide_eq_true_eq,hlabels]
    exact hroot

#print axioms markedNonreal_realized_code_exists
end SpectralRadiusUpperTail
