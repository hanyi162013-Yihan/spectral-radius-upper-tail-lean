import SpectralRadiusUpperTail.MarkedNonrealFlagAtlas
import SpectralRadiusUpperTail.MarkedNonrealWeightMeasurable
import SpectralRadiusUpperTail.RealSchurMixedProductIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

theorem MarkedNonrealFlagAtlas.output_charpoly {m : ℕ} {hm : 0 < m}
    (F : MarkedNonrealFlagAtlas m hm) (k : ℕ)
    (t : RealSchurMixedTangent (markedNonrealBlockSizes m)) :
    ((realSchurMixedEntryEquiv (markedNonrealBlockSizes m)).symm (F.output k t)).charpoly=
      t.2.val.charpoly := by
  rw [MarkedNonrealFlagAtlas.output,realSchurMixedRotatedEntryCoordinates_eq,
    LinearEquiv.symm_apply_apply]
  rw [realMatrixOrthogonalConjugation_charpoly _ _ _ (F.frames k).property]
  rw [realSchurMixedExpCoordinates_eq_conjugation,zero_add,
    realMatrixOrthogonalConjugation_charpoly _ _ _ (realSchurMixedAngularFrame_orthogonal _ t.1)]

theorem MarkedNonrealFlagAtlas.output_code_weight {m : ℕ} {hm : 0 < m}
    (F : MarkedNonrealFlagAtlas m hm) (k : ℕ) (code : MarkedNonrealCode m)
    (t : RealSchurMixedTangent (markedNonrealBlockSizes m)) (ht : t ∈ F.source k code)
    (g : ℂ → ℝ≥0∞) :
    markedNonrealCodeWeight m ((realSchurMixedEntryEquiv (markedNonrealBlockSizes m)).symm
      (F.output k t)) code g = markedNonrealBlockWeight (markedNonrealFirstBlock m t.2.val) g := by
  have hs : t.2.val.charpoly.Separable := ht.2.1
  have hcode : realSchurMixedSpectralCode (markedNonrealBlockSizes m) t.2.val=code := ht.2.2
  have hpoly := F.output_charpoly k t
  rw [markedNonrealCodeWeight_eq_of_charpoly m _ t.2.val (hpoly.symm ▸ hs) hs hpoly]
  rw [← hcode,markedNonrealCodeWeight_upper m hm t.2.val t.2.property hs]

noncomputable def markedNonrealDiagonalWeight (m : ℕ) (g : ℂ → ℝ≥0∞)
    (d : RealSchurMixedDiagonalEntry (markedNonrealBlockSizes m) → ℝ) : ℝ≥0∞ :=
  markedNonrealBlockWeight (markedNonrealFirstBlock m
    (realSchurMixedUpperEntryJoin (markedNonrealBlockSizes m) d 0)) g

theorem markedNonrealDiagonalWeight_measurable (m : ℕ) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    Measurable (markedNonrealDiagonalWeight m g) := by
  apply (markedNonrealBlockWeight_measurable g hg).comp
  have h : Continuous (fun d : RealSchurMixedDiagonalEntry (markedNonrealBlockSizes m) → ℝ =>
      markedNonrealFirstBlock m (realSchurMixedUpperEntryJoin (markedNonrealBlockSizes m) d 0)) := by
    apply continuous_matrix
    intro i j
    simp only [markedNonrealFirstBlock,realSchurMixedUpperEntryJoin]
    simp only [dite_true]
    fun_prop
  exact h.measurable

theorem markedNonrealBlockWeight_eq_diagonal (m : ℕ) (g : ℂ → ℝ≥0∞)
    (t : RealSchurMixedTangent (markedNonrealBlockSizes m)) :
    markedNonrealBlockWeight (markedNonrealFirstBlock m t.2.val) g =
      markedNonrealDiagonalWeight m g (realSchurMixedTangentEntries (markedNonrealBlockSizes m) t).2.1 := by
  have ht : realSchurMixedUpperEntryJoin (markedNonrealBlockSizes m)
      (realSchurMixedTangentEntries (markedNonrealBlockSizes m) t).2.1
      (realSchurMixedTangentEntries (markedNonrealBlockSizes m) t).2.2=t.2.val :=
    congrArg Subtype.val ((realSchurMixedUpperEntryEquiv _).symm_apply_apply t.2)
  have hd := realSchurMixedUpperEntryJoin_diagonalMatrix (markedNonrealBlockSizes m)
    (realSchurMixedTangentEntries (markedNonrealBlockSizes m) t).2.1
    (realSchurMixedTangentEntries (markedNonrealBlockSizes m) t).2.2 0 0
  rw [ht] at hd
  change realSchurMixedDiagonalMatrix (markedNonrealBlockSizes m) t.2.val 0 =
    realSchurMixedDiagonalMatrix (markedNonrealBlockSizes m)
      (realSchurMixedUpperEntryJoin (markedNonrealBlockSizes m)
        (realSchurMixedTangentEntries (markedNonrealBlockSizes m) t).2.1 0) 0 at hd
  exact congrArg (fun B => markedNonrealBlockWeight B g) hd

#print axioms MarkedNonrealFlagAtlas.output_charpoly
#print axioms MarkedNonrealFlagAtlas.output_code_weight
#print axioms markedNonrealDiagonalWeight_measurable
#print axioms markedNonrealBlockWeight_eq_diagonal
end SpectralRadiusUpperTail
