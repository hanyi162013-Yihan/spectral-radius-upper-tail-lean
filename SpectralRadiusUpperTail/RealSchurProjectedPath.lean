import SpectralRadiusUpperTail.MatrixChainProjectionCancel
import SpectralRadiusUpperTail.RealSchurDataProjectionPower
import SpectralRadiusUpperTail.RealSchurPaddedMatrix

namespace SpectralRadiusUpperTail

/-- Along any prescribed block path, restricting the padded chain to its
active endpoint coordinates cancels every intermediate projection. -/
theorem realSchurPaddedPath_projection {N : ℕ} (n l : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (p : Fin (l+1) → Fin N) (m : Fin (l+1) → ℕ) :
    realSchurDataPower (B (p 0)) 0 (z.1 (p 0)) *
      gaussianMatrixChain 2 l
        (fun j => (realSchurDataPower (B (p j)) 1 (z.1 (p j)))^(m j))
        (fun j => realSchurPaddedBridge n B z (p j.castSucc) (p j.succ)) *
      realSchurDataPower (B (p (Fin.last l))) 0 (z.1 (p (Fin.last l))) =
    gaussianMatrixChain 2 l
      (fun j => realSchurDataPower (B (p j)) (m j) (z.1 (p j)))
      (fun j => (1/Real.sqrt n) •
        Matrix.of (fun a b => z.2 ((p j.castSucc,p j.succ),(a,b)))) := by
  have h := matrixChain_projection_cancel 2 l
    (fun j => realSchurDataPower (B (p j)) 0 (z.1 (p j)))
    (fun j => (realSchurDataPower (B (p j)) 1 (z.1 (p j)))^(m j))
    (fun j => realSchurDataPower (B (p j)) (m j) (z.1 (p j)))
    (fun j => (1/Real.sqrt n) •
      Matrix.of (fun a b => z.2 ((p j.castSucc,p j.succ),(a,b))))
    (fun j => realSchurDataPower_projection (B (p j)) (z.1 (p j)) (m j))
  simpa only [realSchurPaddedBridge] using h

#print axioms realSchurPaddedPath_projection
end SpectralRadiusUpperTail
