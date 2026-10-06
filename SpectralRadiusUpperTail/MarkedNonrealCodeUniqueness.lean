import SpectralRadiusUpperTail.MarkedNonrealCoordinates
import SpectralRadiusUpperTail.RealPairComplexRootData
import SpectralRadiusUpperTail.RealSchurMixedCodeMultiplicity

namespace SpectralRadiusUpperTail
open scoped Matrix

theorem markedNonreal_charpoly_product (m : ℕ) (hm : 0 < m)
    (T : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ)
    (hT : realSchurMixedLowerProjection (markedNonrealBlockSizes m) T=0) :
    T.charpoly=(markedNonrealFirstBlock m T).charpoly*(markedNonrealComplement m T).charpoly := by
  rw [realSchurMixed_blockUpper_charpoly _ (markedNonrealBlockSizes_pos m hm) T hT]
  simp only [Fin.prod_univ_two,realSchurMixedDiagonalMatrix_charpoly]
  rfl

theorem markedNonreal_code_eq_of_shared_root (m : ℕ) (hm : 0 < m)
    (T U : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ)
    (hT : realSchurMixedLowerProjection (markedNonrealBlockSizes m) T=0)
    (hU : realSchurMixedLowerProjection (markedNonrealBlockSizes m) U=0)
    (hsep : T.charpoly.Separable) (hpoly : T.charpoly=U.charpoly)
    (z : ℂ) (hz : z.im ≠ 0)
    (ht : ((markedNonrealFirstBlock m T).charpoly.map Complex.ofRealHom).eval z=0)
    (hu : ((markedNonrealFirstBlock m U).charpoly.map Complex.ofRealHom).eval z=0) :
    realSchurMixedSpectralCode (markedNonrealBlockSizes m) T=
      realSchurMixedSpectralCode (markedNonrealBlockSizes m) U := by
  have hfirst := realPair_charpoly_eq_of_shared_nonreal_root
    (markedNonrealFirstBlock m T) (markedNonrealFirstBlock m U) z ht hu hz
  have hrest : (markedNonrealComplement m T).charpoly=(markedNonrealComplement m U).charpoly := by
    apply mul_left_cancel₀ (Matrix.charpoly_monic (markedNonrealFirstBlock m T)).ne_zero
    calc
      _ = T.charpoly := (markedNonreal_charpoly_product m hm T hT).symm
      _ = U.charpoly := hpoly
      _ = _ := by rw [markedNonreal_charpoly_product m hm U hU,hfirst]
  apply realSchurMixedSpectralCode_eq_of_diagonal_polynomials _
    (markedNonrealBlockSizes_pos m hm) T U hT hU hsep
  intro i
  fin_cases i
  · exact hfirst
  · exact hrest

theorem markedNonreal_realized_code_unique
    (m : ℕ) (hm : 0 < m)
    (A : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ)
    (hA : A.charpoly.Separable)
    (c d : Fin 2 → Fin (Fintype.card (RealSchurMixedCoord (markedNonrealBlockSizes m))) → Bool)
    (hc : A ∈ realSchurMixedCodeClass (markedNonrealBlockSizes m) c)
    (hd : A ∈ realSchurMixedCodeClass (markedNonrealBlockSizes m) d)
    (i : Fin (Fintype.card (RealSchurMixedCoord (markedNonrealBlockSizes m))))
    (hi : (realSchurMixedCanonicalSpectrum (markedNonrealBlockSizes m) A i).im ≠ 0)
    (hci : c 0 i=true) (hdi : d 0 i=true) : c=d := by
  let s := markedNonrealBlockSizes m
  obtain ⟨Q,T,hT,hTs,hc,hrepT⟩ := hc
  obtain ⟨R,U,hU,hUs,hd,hrepU⟩ := hd
  have hAT : A.charpoly=T.charpoly := by
    rw [hrepT,realMatrixOrthogonalConjugation_charpoly _ _ _ Q.property]
  have hAU : A.charpoly=U.charpoly := by
    rw [hrepU,realMatrixOrthogonalConjugation_charpoly _ _ _ R.property]
  have hlabelsT := realSchurMixedCanonicalSpectrum_eq_of_charpoly s T A hTs hA hAT.symm
  have hlabelsU := realSchurMixedCanonicalSpectrum_eq_of_charpoly s U A hUs hA hAU.symm
  have ht : ((markedNonrealFirstBlock m T).charpoly.map Complex.ofRealHom).eval
      (realSchurMixedCanonicalSpectrum s A i)=0 := by
    rw [← hc] at hci
    change decide (((markedNonrealFirstBlock m T).charpoly.map Complex.ofRealHom).eval
      (realSchurMixedCanonicalSpectrum s T i)=0)=true at hci
    rw [decide_eq_true_eq,hlabelsT] at hci
    exact hci
  have hu : ((markedNonrealFirstBlock m U).charpoly.map Complex.ofRealHom).eval
      (realSchurMixedCanonicalSpectrum s A i)=0 := by
    rw [← hd] at hdi
    change decide (((markedNonrealFirstBlock m U).charpoly.map Complex.ofRealHom).eval
      (realSchurMixedCanonicalSpectrum s U i)=0)=true at hdi
    rw [decide_eq_true_eq,hlabelsU] at hdi
    exact hdi
  rw [← hc,← hd]
  exact markedNonreal_code_eq_of_shared_root m hm T U hT hU hTs
    (hAT.symm.trans hAU) _ hi ht hu

#print axioms markedNonreal_charpoly_product
#print axioms markedNonreal_code_eq_of_shared_root
#print axioms markedNonreal_realized_code_unique
end SpectralRadiusUpperTail
