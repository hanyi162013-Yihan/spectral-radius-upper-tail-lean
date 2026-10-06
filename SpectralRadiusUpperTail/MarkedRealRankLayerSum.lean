import SpectralRadiusUpperTail.MarkedRealRankGaussianDiagonalFormula
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal Matrix BigOperators

/-- The diagonal Gaussian weight after all real-root ranks are reunited. -/
noncomputable def markedRealSimpleDiagonalWeight
    (m : ℕ) (b : ℝ)
    (d : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ) :
    ℝ≥0∞ :=
  let s := markedRealTwoBlockSizes m
  let S₀ := (realSchurMixedUpperEntryEquiv s).symm
    (d, (0 : RealSchurMixedStrictUpperEntry s → ℝ))
  if S₀ ∈ markedRealUpperSimpleSource m b then
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

/-- Summing the disjoint root-rank layers removes the artificial rank
parameter from the diagonal integral. -/
theorem markedRealRankDiagonalWeight_tsum
    (m : ℕ) (b : ℝ)
    (d : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ) :
    (∑' k : ℕ, markedRealRankDiagonalWeight m k b d) =
      markedRealSimpleDiagonalWeight m b d := by
  let s := markedRealTwoBlockSizes m
  let S₀ := (realSchurMixedUpperEntryEquiv s).symm
    (d, (0 : RealSchurMixedStrictUpperEntry s → ℝ))
  let k₀ := realPolynomialRootRank S₀.val.charpoly
    (markedRealScalar m S₀.val)
  have hzero (k : ℕ) (hk : k ≠ k₀) :
      markedRealRankDiagonalWeight m k b d = 0 := by
    unfold markedRealRankDiagonalWeight
    change (if S₀ ∈ markedRealUpperRankSource m k b then _ else 0) = 0
    rw [if_neg]
    intro h
    exact hk h.2.2.symm
  rw [tsum_eq_single k₀ hzero]
  unfold markedRealRankDiagonalWeight markedRealSimpleDiagonalWeight
  change (if S₀ ∈ markedRealUpperRankSource m k₀ b then _ else 0) =
    (if S₀ ∈ markedRealUpperSimpleSource m b then _ else 0)
  have hiff : S₀ ∈ markedRealUpperRankSource m k₀ b ↔
      S₀ ∈ markedRealUpperSimpleSource m b := by
    change (S₀.val.charpoly.Separable ∧ b < markedRealScalar m S₀.val ∧
      realPolynomialRootRank S₀.val.charpoly
        (markedRealScalar m S₀.val) = k₀) ↔
      (S₀.val.charpoly.Separable ∧ b < markedRealScalar m S₀.val)
    simp [k₀]
  simp only [hiff]

theorem markedRealRankDiagonalWeight_measurable
    (m k : ℕ) (hm : 0 < m) (b : ℝ) :
    Measurable (markedRealRankDiagonalWeight m k b) := by
  have h := (markedRealRankRestWeight_measurable m k b).lintegral_prod_right'
    (ν := (volume : Measure
      (RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m) → ℝ)))
  convert h using 1
  funext d
  exact (markedRealRankRestWeight_lintegral_upper m k hm b d).symm

/-- Local rank layers add to the unranked diagonal Gaussian integral. -/
theorem markedRealRankDiagonalWeight_lintegral_tsum
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∑' k : ℕ, ∫⁻ d, markedRealRankDiagonalWeight m k b d) =
      ∫⁻ d, markedRealSimpleDiagonalWeight m b d := by
  rw [← lintegral_tsum (fun k =>
    (markedRealRankDiagonalWeight_measurable m k hm b).aemeasurable)]
  simp_rw [markedRealRankDiagonalWeight_tsum]

/-- The sum of all local matrix-area integrals has a single diagonal
integral with no root-rank parameter. -/
theorem markedRealAngularRank_gaussian_area_tsum
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∑' k : ℕ,
      ∫⁻ y in
        realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 ''
          (markedRealAngularPositiveSource m ×ˢ
            markedRealUpperRankSource m k b),
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      (∫⁻ ω, markedRealAngularWeight m ω) *
        (∫⁻ d, markedRealSimpleDiagonalWeight m b d) := by
  simp_rw [markedRealAngularRank_gaussian_diagonal_formula m _ hm b]
  rw [ENNReal.tsum_mul_left,
    markedRealRankDiagonalWeight_lintegral_tsum m hm b]

#print axioms markedRealRankDiagonalWeight_tsum
#print axioms markedRealRankDiagonalWeight_lintegral_tsum
#print axioms markedRealAngularRank_gaussian_area_tsum
end SpectralRadiusUpperTail
