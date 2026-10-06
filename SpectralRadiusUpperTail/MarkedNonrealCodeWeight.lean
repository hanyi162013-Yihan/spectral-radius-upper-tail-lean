import SpectralRadiusUpperTail.MarkedNonrealCodeUniqueness
import SpectralRadiusUpperTail.RealPairUpperRoot
import SpectralRadiusUpperTail.RealSchurCanonicalSpectrumSimple

namespace SpectralRadiusUpperTail
open scoped ENNReal

noncomputable def markedNonrealCodeWeight (m : ℕ)
    (A : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ)
    (code : Fin 2 → Fin (Fintype.card (RealSchurMixedCoord (markedNonrealBlockSizes m))) → Bool)
    (g : ℂ → ℝ≥0∞) : ℝ≥0∞ := by
  classical
  exact ∑ i, if code 0 i=true ∧
    0 < (realSchurMixedCanonicalSpectrum (markedNonrealBlockSizes m) A i).im then
    g (realSchurMixedCanonicalSpectrum (markedNonrealBlockSizes m) A i) else 0

noncomputable def markedNonrealBlockWeight (B : Matrix (Fin 2) (Fin 2) ℝ)
    (g : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  if 0 < realPairHeightSq B then g (realPairUpperRoot B) else 0

/-- A code's upper-half-plane weight is exactly the weight of its first
nonreal block, and is zero when that block has only real roots. -/
theorem markedNonrealCodeWeight_upper
    (m : ℕ) (hm : 0 < m)
    (T : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ)
    (hT : realSchurMixedLowerProjection (markedNonrealBlockSizes m) T=0)
    (hsep : T.charpoly.Separable) (g : ℂ → ℝ≥0∞) :
    markedNonrealCodeWeight m T (realSchurMixedSpectralCode (markedNonrealBlockSizes m) T) g =
      markedNonrealBlockWeight (markedNonrealFirstBlock m T) g := by
  classical
  let s := markedNonrealBlockSizes m
  let B := markedNonrealFirstBlock m T
  let z := realSchurMixedCanonicalSpectrum s T
  have hroot (i : Fin (Fintype.card (RealSchurMixedCoord s)))
      (hi : realSchurMixedSpectralCode s T 0 i=true) :
      (B.charpoly.map Complex.ofRealHom).eval (z i)=0 := by
    exact of_decide_eq_true hi
  change (∑ i, if realSchurMixedSpectralCode s T 0 i=true ∧ 0 < (z i).im then g (z i) else 0)=_
  by_cases hB : 0 < realPairHeightSq B
  · change _ = if 0 < realPairHeightSq B then g (realPairUpperRoot B) else 0
    rw [if_pos hB]
    have hd : B.charpoly ∣ T.charpoly :=
      realSchurMixedDiagonalMatrix_charpoly_dvd s (markedNonrealBlockSizes_pos m hm) T hT 0
    have hz : (T.charpoly.map Complex.ofRealHom).eval (realPairUpperRoot B)=0 :=
      Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd _ hd)
        (realPairUpperRoot_isRoot B hB.le)
    obtain ⟨i,hi⟩ := realSchurMixedCanonicalSpectrum_covers s T hsep _ hz
    change z i=realPairUpperRoot B at hi
    have hic : realSchurMixedSpectralCode s T 0 i=true := by
      apply decide_eq_true
      change (B.charpoly.map Complex.ofRealHom).eval (z i)=0
      rw [hi]
      exact realPairUpperRoot_isRoot B hB.le
    rw [Finset.sum_eq_single i]
    · change (if realSchurMixedSpectralCode s T 0 i=true ∧ 0 < (z i).im then g (z i) else 0)=_
      rw [if_pos ⟨hic,hi.symm ▸ realPairUpperRoot_pos B hB⟩,hi]
    · intro j hj hji
      by_cases hp : realSchurMixedSpectralCode s T 0 j=true ∧ 0 < (z j).im
      · have hzr := realPairUpperRoot_eq_of_root B (z j) (hroot j hp.1) hp.2
        have he : j=i := realSchurMixedCanonicalSpectrum_injective s T hsep (hzr.symm.trans hi.symm)
        exact False.elim (hji he)
      · exact if_neg hp
    · simp
  · change _ = if 0 < realPairHeightSq B then g (realPairUpperRoot B) else 0
    rw [if_neg hB]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hp : realSchurMixedSpectralCode s T 0 i=true ∧ 0 < (z i).im
    · have hh := (realPair_nonreal_root_data B (z i) (hroot i hp.1) (ne_of_gt hp.2)).2
      exact False.elim (hB (hh.symm ▸ sq_pos_of_ne_zero (ne_of_gt hp.2)))
    · exact if_neg hp

#print axioms markedNonrealCodeWeight_upper
end SpectralRadiusUpperTail
