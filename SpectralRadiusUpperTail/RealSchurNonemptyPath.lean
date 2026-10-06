import SpectralRadiusUpperTail.MatrixChainProjectionNonempty
import SpectralRadiusUpperTail.RealSchurDataProjectionPower
import SpectralRadiusUpperTail.RealSchurPaddedMatrix

namespace SpectralRadiusUpperTail

/-- Every nonempty padded Schur bridge chain is exactly the corresponding
raw Gaussian bridge chain, including zero waiting times. -/
theorem realSchurPaddedPath_nonempty {N : ℕ} (n l : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (p : Fin (l+1+1) → Fin N) (m : Fin (l+1+1) → ℕ) :
    gaussianMatrixChain 2 (l+1)
        (fun j => (realSchurDataPower (B (p j)) 1 (z.1 (p j)))^(m j))
        (fun j => realSchurPaddedBridge n B z (p j.castSucc) (p j.succ)) =
      gaussianMatrixChain 2 (l+1)
        (fun j => realSchurDataPower (B (p j)) (m j) (z.1 (p j)))
        (fun j => (1/Real.sqrt n) •
          Matrix.of (fun a b => z.2 ((p j.castSucc,p j.succ),(a,b)))) := by
  have h := matrixChain_projection_cancel_nonempty 2 l
    (fun j => realSchurDataPower (B (p j)) 0 (z.1 (p j)))
    (fun j => (realSchurDataPower (B (p j)) 1 (z.1 (p j)))^(m j))
    (fun j => realSchurDataPower (B (p j)) (m j) (z.1 (p j)))
    (fun j => (1/Real.sqrt n) •
      Matrix.of (fun a b => z.2 ((p j.castSucc,p j.succ),(a,b))))
    (fun j => realSchurDataPower_projection (B (p j)) (z.1 (p j)) (m j))
    (realSchurDataPower_projection_left (B (p 0)) (z.1 (p 0)) (m 0))
    (realSchurDataPower_projection_right
      (B (p (Fin.last (l+1)))) (z.1 (p (Fin.last (l+1))))
      (m (Fin.last (l+1))))
  simpa only [realSchurPaddedBridge] using h

#print axioms realSchurPaddedPath_nonempty
end SpectralRadiusUpperTail
