import SpectralRadiusUpperTail.RealSchurFixedStartGaussianSum
import SpectralRadiusUpperTail.RealSchurZeroEdgeGaussian

namespace SpectralRadiusUpperTail
open scoped BigOperators

theorem realSchurFixedStartPathSum_gaussian_all {N : ℕ}
    (n k l : ℕ) (hk : 0 < k)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (i j : Fin N) :
    schurFixedStartPathSum 2 N l k
        (realSchurPaddedDiagonal B z)
        (realSchurPaddedStrictUpper n B z) i j =
      ∑ p : {p : IncreasingBlockPath N l // p.val 0 = i},
        if p.val.val (Fin.last l) = j then
          realSchurGlobalWaitingSum n k B ⟨l,p.val⟩ z else 0 := by
  cases l with
  | zero => exact realSchurFixedStartPathSum_zero_gaussian n k hk B z i j
  | succ l => exact realSchurFixedStartPathSum_gaussian n k l B z i j

#print axioms realSchurFixedStartPathSum_gaussian_all
end SpectralRadiusUpperTail
