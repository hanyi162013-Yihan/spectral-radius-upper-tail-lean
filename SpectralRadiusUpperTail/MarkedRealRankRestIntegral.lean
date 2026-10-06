import SpectralRadiusUpperTail.MarkedRealRankWeights
import SpectralRadiusUpperTail.MarkedRealRankGaussianUpperFiber
import SpectralRadiusUpperTail.RealSchurMixedGaussianUpperLIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal Matrix BigOperators

/-- After the free Gaussian upper row is removed, the rank-layer
integrand is a function only of the scalar and complementary block entries. -/
noncomputable def markedRealRankDiagonalWeight
    (m k : ℕ) (b : ℝ)
    (d : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ) :
    ℝ≥0∞ :=
  let s := markedRealTwoBlockSizes m
  let S₀ := (realSchurMixedUpperEntryEquiv s).symm
    (d, (0 : RealSchurMixedStrictUpperEntry s → ℝ))
  if S₀ ∈ markedRealUpperRankSource m k b then
    ENNReal.ofReal
      |(markedRealComplement m S₀.val -
        markedRealScalar m S₀.val •
          (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
      (ENNReal.ofReal
        (Real.exp (-(∑ p : RealSchurMixedDiagonalEntry s,
          (d p)^2)/2)) *
        ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
          (Fintype.card (RealSchurMixedStrictUpperEntry s))))
  else 0

theorem markedRealRankRestWeight_lintegral_upper
    (m k : ℕ) (hm : 0 < m) (b : ℝ)
    (d : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ) :
    (∫⁻ u : RealSchurMixedStrictUpperEntry
        (markedRealTwoBlockSizes m) → ℝ,
      markedRealRankRestWeight m k b (d,u)) =
        markedRealRankDiagonalWeight m k b d := by
  let s := markedRealTwoBlockSizes m
  let S (u : RealSchurMixedStrictUpperEntry s → ℝ) :=
    (realSchurMixedUpperEntryEquiv s).symm (d,u)
  have hguard (u : RealSchurMixedStrictUpperEntry s → ℝ) :
      S u ∈ markedRealUpperRankSource m k b ↔
        S 0 ∈ markedRealUpperRankSource m k b :=
    markedRealUpperRank_fiber_const m k hm b 0 d u 0
  have hscalar (u : RealSchurMixedStrictUpperEntry s → ℝ) :
      markedRealScalar m (S u).val =
        markedRealScalar m (S 0).val := by
    change markedRealScalar m (realSchurMixedUpperEntryJoin s d u) =
      markedRealScalar m (realSchurMixedUpperEntryJoin s d 0)
    simp [markedRealScalar, realSchurMixedUpperEntryJoin]
  have hcomp (u : RealSchurMixedStrictUpperEntry s → ℝ) :
      markedRealComplement m (S u).val =
        markedRealComplement m (S 0).val := by
    ext i j
    change (realSchurMixedUpperEntryJoin s d u) ⟨1,i⟩ ⟨1,j⟩ =
      (realSchurMixedUpperEntryJoin s d 0) ⟨1,i⟩ ⟨1,j⟩
    simp [realSchurMixedUpperEntryJoin]
  have hdet (u : RealSchurMixedStrictUpperEntry s → ℝ) :
      |(markedRealComplement m (S u).val -
        markedRealScalar m (S u).val •
          (1 : Matrix (Fin m) (Fin m) ℝ)).det| =
      |(markedRealComplement m (S 0).val -
        markedRealScalar m (S 0).val •
          (1 : Matrix (Fin m) (Fin m) ℝ)).det| := by
    rw [hscalar u, hcomp u]
  by_cases h0 : S 0 ∈ markedRealUpperRankSource m k b
  · have hu (u : RealSchurMixedStrictUpperEntry s → ℝ) :
      S u ∈ markedRealUpperRankSource m k b := (hguard u).mpr h0
    have hpoint (u : RealSchurMixedStrictUpperEntry s → ℝ) :
        markedRealRankRestWeight m k b (d,u) =
          ENNReal.ofReal
            |(markedRealComplement m (S 0).val -
              markedRealScalar m (S 0).val •
                (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
            ENNReal.ofReal (realMatrixGaussianWeight
              (RealSchurMixedCoord s)
                (realSchurMixedUpperEntryJoin s d u)) := by
      change (if S u ∈ markedRealUpperRankSource m k b then
        ENNReal.ofReal
          |(markedRealComplement m (S u).val -
            markedRealScalar m (S u).val •
              (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
          ENNReal.ofReal (realMatrixGaussianWeight
            (RealSchurMixedCoord s) (S u).val)
        else 0) = _
      rw [if_pos (hu u), hdet u]
      rfl
    simp_rw [hpoint]
    rw [lintegral_const_mul']
    · rw [realSchurMixedGaussianWeight_lintegral_upper]
      change _ = (if S 0 ∈ markedRealUpperRankSource m k b then _ else 0)
      rw [if_pos h0]
    · simp
  · have hu (u : RealSchurMixedStrictUpperEntry s → ℝ) :
      S u ∉ markedRealUpperRankSource m k b := by
      intro h
      exact h0 ((hguard u).mp h)
    have hzero (u : RealSchurMixedStrictUpperEntry s → ℝ) :
        markedRealRankRestWeight m k b (d,u) = 0 := by
      change (if S u ∈ markedRealUpperRankSource m k b then _ else 0) = 0
      rw [if_neg (hu u)]
    simp_rw [hzero]
    simp only [lintegral_zero]
    change 0 = (if S 0 ∈ markedRealUpperRankSource m k b then _ else 0)
    rw [if_neg h0]

/-- Tonelli now removes the entire free upper row from the rank-layer
Gaussian integral. Only the scalar and complementary matrix entries remain. -/
theorem markedRealRankRestWeight_lintegral_diagonal
    (m k : ℕ) (hm : 0 < m) (b : ℝ) :
    (∫⁻ z : (RealSchurMixedDiagonalEntry
          (markedRealTwoBlockSizes m) → ℝ) ×
        (RealSchurMixedStrictUpperEntry
          (markedRealTwoBlockSizes m) → ℝ),
      markedRealRankRestWeight m k b z) =
      ∫⁻ d, markedRealRankDiagonalWeight m k b d := by
  change (∫⁻ z : (RealSchurMixedDiagonalEntry
        (markedRealTwoBlockSizes m) → ℝ) ×
      (RealSchurMixedStrictUpperEntry
        (markedRealTwoBlockSizes m) → ℝ),
      markedRealRankRestWeight m k b z
        ∂((volume : Measure (RealSchurMixedDiagonalEntry
          (markedRealTwoBlockSizes m) → ℝ)).prod
          (volume : Measure (RealSchurMixedStrictUpperEntry
            (markedRealTwoBlockSizes m) → ℝ)))) = _
  rw [lintegral_prod _
    (markedRealRankRestWeight_measurable m k b).aemeasurable]
  simp_rw [markedRealRankRestWeight_lintegral_upper m k hm b]

#print axioms markedRealRankRestWeight_lintegral_upper
#print axioms markedRealRankRestWeight_lintegral_diagonal
end SpectralRadiusUpperTail
