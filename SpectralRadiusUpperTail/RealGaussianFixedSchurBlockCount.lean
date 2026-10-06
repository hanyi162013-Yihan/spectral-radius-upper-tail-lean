import SpectralRadiusUpperTail.RealGaussianExteriorUnscaledCount
import SpectralRadiusUpperTail.RealSchurFixedChartRootCounts
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Exterior roots contributed by the diagonal blocks of one fixed
mixed-Schur chart output, with matrix normalization inside the test. -/
noncomputable def realSchurFixedDiagonalExteriorCount
    {n : ℕ} (c : RealSchurFixedChartIndex n)
    (t : RealSchurMixedTangent (realSchurListBlockSize c.shape))
    (r : ℝ) (i : Fin 3) : ℕ := by
  classical
  exact ∑ j : Fin c.shape.length,
    Multiset.countP
      (fun z : ℂ => realGaussianExteriorPredicate r i
        ((((1/Real.sqrt (n : ℝ)) : ℝ) : ℂ) * z))
      (((c.frame.T+t.2.val).toSquareBlock
        (fun z : RealSchurMixedCoord (realSchurListBlockSize c.shape) => z.1)
        j).charpoly.aroots ℂ)

/-- The normalized root count of the original fixed matrix output is
exactly the sum of its diagonal-block counts, at every chart parameter. -/
theorem realGaussianExteriorCount_fixedChartOutput
    {n : ℕ} (hn : 0 < n) (c : RealSchurFixedChartIndex n)
    (t : RealSchurMixedTangent (realSchurListBlockSize c.shape))
    (r : ℝ) (i : Fin 3) :
    realGaussianExteriorCount n r i
      (realSchurFixedChartOutputEntries c t) =
        (realSchurFixedDiagonalExteriorCount c t r i : ℝ) := by
  classical
  rw [realGaussianExteriorCount_eq_unscaled_countP n hn r i]
  change ((Multiset.countP
    (fun z : ℂ => realGaussianExteriorPredicate r i
      ((((1/Real.sqrt (n : ℝ)) : ℝ) : ℂ) * z))
    ((Matrix.of (realSchurFixedChartOutputEntries c t).curry).charpoly.aroots ℂ) : ℕ) : ℝ) =
      ((∑ j : Fin c.shape.length,
        Multiset.countP
          (fun z : ℂ => realGaussianExteriorPredicate r i
            ((((1/Real.sqrt (n : ℝ)) : ℝ) : ℂ) * z))
          (((c.frame.T+t.2.val).toSquareBlock
            (fun z : RealSchurMixedCoord (realSchurListBlockSize c.shape) => z.1)
            j).charpoly.aroots ℂ) : ℕ) : ℝ)
  congr 1
  exact realSchurFixedChartOutput_rootCountP c t _

#print axioms realGaussianExteriorCount_fixedChartOutput
end SpectralRadiusUpperTail
