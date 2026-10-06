import SpectralRadiusUpperTail.MatrixChainExpansion

namespace SpectralRadiusUpperTail

lemma matrixChain_scale_random {d : ℕ} (t : ℝ) (l : ℕ)
    (D : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ)
    (G : Fin l → Matrix (Fin d) (Fin d) ℝ) :
    gaussianMatrixChain d l D (fun j => t • G j) = t^l • gaussianMatrixChain d l D G := by
  induction l with
  | zero => simp [gaussianMatrixChain]
  | succ l ih =>
    simp only [gaussianMatrixChain, ih, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ]
    congr 1
    ring

#print axioms matrixChain_scale_random
end SpectralRadiusUpperTail
