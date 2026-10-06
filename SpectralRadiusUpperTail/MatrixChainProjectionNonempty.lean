import SpectralRadiusUpperTail.MatrixChainEndpointSupport

namespace SpectralRadiusUpperTail

/-- In a nonempty chain the first and final bridges supply the endpoint
projections, so the projected chain equals the unprojected supported chain. -/
theorem matrixChain_projection_cancel_nonempty (d l : ℕ)
    (P C A : Fin (l+1+1) → Matrix (Fin d) (Fin d) ℝ)
    (G : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ)
    (hproj : ∀ i, P i * C i * P i = A i)
    (hleft : P 0 * C 0 * P 0 = C 0 * P 0)
    (hright : P (Fin.last (l+1)) * C (Fin.last (l+1)) *
        P (Fin.last (l+1)) =
      P (Fin.last (l+1)) * C (Fin.last (l+1))) :
    gaussianMatrixChain d (l+1) C
        (fun j => P j.castSucc * G j * P j.succ) =
      gaussianMatrixChain d (l+1) A G := by
  have hL := matrixChain_projection_left_support d l P C G hleft
  have hR := matrixChain_projection_right_support d l P C G hright
  have hP := matrixChain_projection_cancel d (l+1) P C A G hproj
  calc
    gaussianMatrixChain d (l+1) C
        (fun j => P j.castSucc * G j * P j.succ) =
      P 0 * gaussianMatrixChain d (l+1) C
        (fun j => P j.castSucc * G j * P j.succ) *
          P (Fin.last (l+1)) := by rw [hL, hR]
    _ = gaussianMatrixChain d (l+1) A G := hP

#print axioms matrixChain_projection_cancel_nonempty
end SpectralRadiusUpperTail
