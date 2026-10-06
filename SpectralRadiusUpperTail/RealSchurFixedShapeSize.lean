import SpectralRadiusUpperTail.RealSchurFixedCountableAtlas
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Every block of an indexed fixed real-Schur chart has size one or two. -/
theorem RealSchurFixedChartIndex.blockSize_cases
    {n : ℕ} (c : RealSchurFixedChartIndex n)
    (j : Fin c.shape.length) :
    realSchurListBlockSize c.shape j = 1 ∨
      realSchurListBlockSize c.shape j = 2 :=
  c.small _ (realSchurListBlockSize_mem c.shape j)

/-- The sizes of the diagonal blocks account for every matrix coordinate. -/
theorem RealSchurFixedChartIndex.sum_blockSizes
    {n : ℕ} (c : RealSchurFixedChartIndex n) :
    (∑ j : Fin c.shape.length, realSchurListBlockSize c.shape j) = n := by
  have h := Fintype.card_congr c.indexEquiv
  simpa only [Fintype.card_fin, Fintype.card_sigma] using h.symm

#print axioms RealSchurFixedChartIndex.sum_blockSizes
end SpectralRadiusUpperTail
