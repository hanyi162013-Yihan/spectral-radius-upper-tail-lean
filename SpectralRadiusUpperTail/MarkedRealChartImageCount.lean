import SpectralRadiusUpperTail.MarkedRealChartImageFiber
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Set
open scoped ENNReal

private abbrev MarkedMatrix (m : ℕ) :=
  Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
    (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ

/-- Count distinct real roots above the cutoff on the simple-spectrum
locus, and zero elsewhere. This is the exact multiplicity of the marked
chart image family. -/
noncomputable def markedRealSimpleRootCount (m : ℕ) (b : ℝ)
    (A : MarkedMatrix m) : ℝ≥0∞ :=
  ({x : ℝ | A.charpoly.Separable ∧
      A.charpoly.IsRoot x ∧ b < x}.encard : ℝ≥0∞)

theorem markedRealChart_matrixImage_encard
    (m : ℕ) (hm : 0 < m) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (hcover :
      (⋃ k, markedRealIncidenceFirstPatch m b c k) = Set.univ)
    (A : MarkedMatrix m) :
    {k : ℕ | A ∈ (c k).chart ''
      markedRealChartFirstSource m b c k}.encard =
      {x : ℝ | A.charpoly.Separable ∧
        A.charpoly.IsRoot x ∧ b < x}.encard := by
  by_cases hsep : A.charpoly.Separable
  · simp only [hsep, true_and]
    simp_rw [markedRealChartFirstSource_matrixImage m hm b c]
    exact markedRealIncidenceFirstPatch_fiberCount
      m hm b c hcover A hsep
  · simp only [hsep, false_and, Set.setOf_false, Set.encard_empty]
    have hempty : {k : ℕ | A ∈ (c k).chart ''
        markedRealChartFirstSource m b c k} = ∅ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨t,ht,hA⟩
      have hsep' : ((c k).chart t).charpoly.Separable := ht.1.2
      rw [hA] at hsep'
      exact hsep hsep'
    rw [hempty, Set.encard_empty]

theorem markedRealChart_entryImage_encard
    (m : ℕ) (hm : 0 < m) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (hcover :
      (⋃ k, markedRealIncidenceFirstPatch m b c k) = Set.univ)
    (y : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
    {k : ℕ | y ∈ markedRealChartEntryImage m b c k}.encard =
      {x : ℝ |
        ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y).charpoly.Separable ∧
        ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y).charpoly.IsRoot x ∧
          b < x}.encard := by
  have heq :
      {k : ℕ | y ∈ markedRealChartEntryImage m b c k} =
        {k : ℕ |
          (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y ∈
            (c k).chart '' markedRealChartFirstSource m b c k} := by
    ext k
    change y ∈ realSchurMixedEntryEquiv (markedRealTwoBlockSizes m) ''
        ((c k).chart '' markedRealChartFirstSource m b c k) ↔
      (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y ∈
        (c k).chart '' markedRealChartFirstSource m b c k
    constructor
    · rintro ⟨A,hA,hAy⟩
      have h := congrArg
        (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm hAy
      rw [(realSchurMixedEntryEquiv
        (markedRealTwoBlockSizes m)).symm_apply_apply] at h
      rw [← h]
      exact hA
    · intro h
      exact ⟨(realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y,
        h, (realSchurMixedEntryEquiv
          (markedRealTwoBlockSizes m)).apply_symm_apply y⟩
  rw [heq]
  exact markedRealChart_matrixImage_encard m hm b c hcover _

#print axioms markedRealChart_matrixImage_encard
#print axioms markedRealChart_entryImage_encard
end SpectralRadiusUpperTail
