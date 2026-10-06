import SpectralRadiusUpperTail.MarkedRealRankFiberConst
import SpectralRadiusUpperTail.RealSchurMixedGaussianFiber
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open Classical
open scoped Matrix BigOperators

/-- The rank-layer guard is constant as the free upper row varies. -/
theorem markedRealUpperRank_fiber_const
    (m k : ℕ) (hm : 0 < m) (b : ℝ)
    (ω : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ)
    (d : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ)
    (u v : RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m) → ℝ) :
    (realSchurMixedFiberPoint (markedRealTwoBlockSizes m) ω d u).2 ∈
        markedRealUpperRankSource m k b ↔
      (realSchurMixedFiberPoint (markedRealTwoBlockSizes m) ω d v).2 ∈
        markedRealUpperRankSource m k b := by
  apply markedRealUpperRankSource_iff_of_diagonal_blocks m k hm b
  intro i a c
  simp only [realSchurMixedFiberPoint_upper]
  simp [realSchurMixedUpperEntryJoin]

/-- The free Gaussian upper row integrates to its exact normalizer even
after restricting to one real-root rank. The rank indicator stays in the
diagonal-block variables. -/
theorem markedRealGaussianJacobian_integral_upper_rank
    (m k : ℕ) (hm : 0 < m) (b : ℝ)
    (ω : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ)
    (d : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ) :
    (∫ u : RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m) → ℝ,
      if (realSchurMixedFiberPoint (markedRealTwoBlockSizes m) ω d u).2 ∈
          markedRealUpperRankSource m k b then
        realSchurMixedJacobianWeight (markedRealTwoBlockSizes m) 0
          (realSchurMixedFiberPoint (markedRealTwoBlockSizes m) ω d u) *
            realMatrixGaussianWeight
              (RealSchurMixedCoord (markedRealTwoBlockSizes m))
                (realSchurMixedFiberPoint
                  (markedRealTwoBlockSizes m) ω d u).2.val
      else 0) =
    if (realSchurMixedFiberPoint (markedRealTwoBlockSizes m) ω d 0).2 ∈
        markedRealUpperRankSource m k b then
      realSchurMixedJacobianWeight (markedRealTwoBlockSizes m) 0
        (realSchurMixedFiberPoint (markedRealTwoBlockSizes m) ω d 0) *
          (Real.exp (-(∑ p : RealSchurMixedDiagonalEntry
            (markedRealTwoBlockSizes m), (d p)^2)/2) *
            (Real.sqrt (2*Real.pi)) ^
              (Fintype.card (RealSchurMixedStrictUpperEntry
                (markedRealTwoBlockSizes m))))
    else 0 := by
  classical
  by_cases h0 :
      (realSchurMixedFiberPoint (markedRealTwoBlockSizes m) ω d 0).2 ∈
        markedRealUpperRankSource m k b
  · have hu (u : RealSchurMixedStrictUpperEntry
        (markedRealTwoBlockSizes m) → ℝ) :
      (realSchurMixedFiberPoint (markedRealTwoBlockSizes m) ω d u).2 ∈
        markedRealUpperRankSource m k b :=
      (markedRealUpperRank_fiber_const m k hm b ω d u 0).mpr h0
    simp only [h0, if_true]
    have hfun : (fun u : RealSchurMixedStrictUpperEntry
        (markedRealTwoBlockSizes m) → ℝ =>
        if (realSchurMixedFiberPoint (markedRealTwoBlockSizes m) ω d u).2 ∈
            markedRealUpperRankSource m k b then
          realSchurMixedJacobianWeight (markedRealTwoBlockSizes m) 0
            (realSchurMixedFiberPoint (markedRealTwoBlockSizes m) ω d u) *
              realMatrixGaussianWeight
                (RealSchurMixedCoord (markedRealTwoBlockSizes m))
                  (realSchurMixedFiberPoint
                    (markedRealTwoBlockSizes m) ω d u).2.val
        else 0) =
      (fun u => realSchurMixedJacobianWeight (markedRealTwoBlockSizes m) 0
          (realSchurMixedFiberPoint (markedRealTwoBlockSizes m) ω d u) *
            realMatrixGaussianWeight
              (RealSchurMixedCoord (markedRealTwoBlockSizes m))
                (realSchurMixedFiberPoint
                  (markedRealTwoBlockSizes m) ω d u).2.val) := by
      funext u
      simp [hu u]
    rw [hfun]
    exact realSchurMixedGaussianJacobian_integral_upper
      (markedRealTwoBlockSizes m) ω d
  · have hu (u : RealSchurMixedStrictUpperEntry
        (markedRealTwoBlockSizes m) → ℝ) :
      (realSchurMixedFiberPoint (markedRealTwoBlockSizes m) ω d u).2 ∉
        markedRealUpperRankSource m k b := by
      intro h
      exact h0 ((markedRealUpperRank_fiber_const m k hm b ω d u 0).mp h)
    simp [h0, hu]

#print axioms markedRealGaussianJacobian_integral_upper_rank
end SpectralRadiusUpperTail
