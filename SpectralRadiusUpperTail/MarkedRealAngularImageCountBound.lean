import SpectralRadiusUpperTail.MarkedRealAngularImageRankBound
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Set

/-- At one matrix, distinct rank-layer images correspond to distinct
actual real roots. The fixed-chart layer sum never overcounts roots. -/
theorem markedRealAngularRank_image_encard_le_root_encard
    (m : ℕ) (hm : 0 < m) (b : ℝ)
    (y : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
    {k : ℕ | y ∈
      realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 ''
        (markedRealAngularPositiveSource m ×ˢ
          markedRealUpperRankSource m k b)}.encard ≤
      {x : ℝ |
        ((realSchurMixedEntryEquiv
          (markedRealTwoBlockSizes m)).symm y).charpoly.Separable ∧
        ((realSchurMixedEntryEquiv
          (markedRealTwoBlockSizes m)).symm y).charpoly.IsRoot x ∧
        b < x}.encard := by
  classical
  let A := (realSchurMixedEntryEquiv
    (markedRealTwoBlockSizes m)).symm y
  let I : Set ℕ := {k | y ∈
    realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 ''
      (markedRealAngularPositiveSource m ×ˢ
        markedRealUpperRankSource m k b)}
  let R : Set ℝ := {x | A.charpoly.Separable ∧
    A.charpoly.IsRoot x ∧ b < x}
  have hr (k : ℕ) (hk : k ∈ I) :
      A.charpoly.Separable ∧
        ∃ x : ℝ, A.charpoly.IsRoot x ∧ b < x ∧
          realPolynomialRootRank A.charpoly x = k :=
    markedRealAngularRank_image_has_rankedRoot m k hm b y hk
  let f (k : ℕ) : ℝ :=
    if hk : k ∈ I then Classical.choose (hr k hk).2 else 0
  have hf (k : ℕ) (hk : k ∈ I) :
      A.charpoly.IsRoot (f k) ∧ b < f k ∧
        realPolynomialRootRank A.charpoly (f k) = k := by
    simpa only [f, dif_pos hk] using
      (Classical.choose_spec (hr k hk).2)
  have hmap : MapsTo f I R := by
    intro k hk
    exact ⟨(hr k hk).1, (hf k hk).1, (hf k hk).2.1⟩
  have hinj : InjOn f I := by
    intro k hk l hl heq
    calc
      k = realPolynomialRootRank A.charpoly (f k) := (hf k hk).2.2.symm
      _ = realPolynomialRootRank A.charpoly (f l) := by rw [heq]
      _ = l := (hf l hl).2.2
  change I.encard ≤ R.encard
  exact Set.encard_le_encard_of_injOn hmap hinj

#print axioms markedRealAngularRank_image_encard_le_root_encard
end SpectralRadiusUpperTail
