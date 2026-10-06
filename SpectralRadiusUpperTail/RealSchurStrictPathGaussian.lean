import SpectralRadiusUpperTail.RealSchurNonemptyPath
import SpectralRadiusUpperTail.RealSchurPaddedPathExpansion
import SpectralRadiusUpperTail.MatrixChainScaling
import SpectralRadiusUpperTail.SchurMatrixPathSum

namespace SpectralRadiusUpperTail

/-- A nonempty strict path in the actual padded matrix-power expansion is
the same Gaussian matrix-chain term used in the global product model. -/
theorem realSchurStrictPathTerm_gaussian {N : ℕ} (n l : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (p : IncreasingBlockPath N (l+1)) (m : Fin (l+1+1) → ℕ) :
    schurStrictPathTerm 2 N (l+1)
        (realSchurPaddedDiagonal B z)
        (realSchurPaddedStrictUpper n B z) p.val m =
      (1/Real.sqrt n)^(l+1) •
        schurPathMatrix (⟨l+1,p⟩ : AnyIncreasingPath N)
          (fun j => realSchurDataPower (B (p.val j)) (m j) (z.1 (p.val j))) z.2 := by
  have hstrict (j : Fin (l+1)) : p.val j.castSucc < p.val j.succ :=
    p.property j.castSucc_lt_succ
  have hU :
      (fun j : Fin (l+1) => realSchurPaddedStrictUpper n B z
        (p.val j.castSucc) (p.val j.succ)) =
      (fun j => realSchurPaddedBridge n B z
        (p.val j.castSucc) (p.val j.succ)) := by
    funext j
    simp [realSchurPaddedStrictUpper, hstrict j]
  calc
    schurStrictPathTerm 2 N (l+1)
        (realSchurPaddedDiagonal B z)
        (realSchurPaddedStrictUpper n B z) p.val m =
      gaussianMatrixChain 2 (l+1)
        (fun j => (realSchurDataPower (B (p.val j)) 1 (z.1 (p.val j)))^(m j))
        (fun j => realSchurPaddedBridge n B z (p.val j.castSucc) (p.val j.succ)) := by
      unfold schurStrictPathTerm
      simpa only [realSchurPaddedDiagonal, hU]
    _ = gaussianMatrixChain 2 (l+1)
        (fun j => realSchurDataPower (B (p.val j)) (m j) (z.1 (p.val j)))
        (fun j => (1/Real.sqrt n) •
          Matrix.of (fun a b => z.2 ((p.val j.castSucc,p.val j.succ),(a,b)))) :=
      realSchurPaddedPath_nonempty n l B z p.val m
    _ = _ := by
      rw [matrixChain_scale_random]
      rfl

#print axioms realSchurStrictPathTerm_gaussian
end SpectralRadiusUpperTail
