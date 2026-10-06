import SpectralRadiusUpperTail.RealSchurMixedChartRoots
import Mathlib.Data.Multiset.Bind
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Counting a predicate after concatenating multisets is the sum of
the individual counts; multiplicities are retained. -/
theorem realSchurMixed_countP_bind
    {α β : Type*} (p : α → Prop) [DecidablePred p]
    (s : Multiset β) (f : β → Multiset α) :
    Multiset.countP p (s.bind f) =
      (s.map (fun i => Multiset.countP p (f i))).sum := by
  simp only [Multiset.countP_eq_card_filter,
    Multiset.filter_bind, Multiset.card_bind, Function.comp_def]

/-- Any complex-root counting statistic of a genuine mixed real-Schur
chart is the sum of the same statistic over its current diagonal blocks. -/
theorem realSchurMixedExpCoordinates_aroots_countP
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (x : RealSchurMixedTangent s)
    (p : ℂ → Prop) [DecidablePred p] :
    Multiset.countP p
      ((realSchurMixedExpCoordinates s T x).charpoly.aroots ℂ) =
      ∑ i : Fin m, Multiset.countP p
        (((T+x.2.val).toSquareBlock
          (fun z : RealSchurMixedCoord s => z.1) i).charpoly.aroots ℂ) := by
  rw [realSchurMixedExpCoordinates_aroots s hs T hT x,
    realSchurMixed_countP_bind]
  rfl

#print axioms realSchurMixedExpCoordinates_aroots_countP
end SpectralRadiusUpperTail
