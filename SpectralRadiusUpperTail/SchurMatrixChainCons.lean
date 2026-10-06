import SpectralRadiusUpperTail.MatrixChainExpansion

namespace SpectralRadiusUpperTail

/-- Split a nonempty Schur matrix chain at its first bridge. -/
theorem gaussianMatrixChain_cons (d l : ℕ)
    (D0 : Matrix (Fin d) (Fin d) ℝ)
    (D : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ)
    (G0 : Matrix (Fin d) (Fin d) ℝ)
    (G : Fin l → Matrix (Fin d) (Fin d) ℝ) :
    gaussianMatrixChain d (l+1) (Fin.cons D0 D) (Fin.cons G0 G) =
      D0 * G0 * gaussianMatrixChain d l D G := by
  induction l with
  | zero =>
    simp [gaussianMatrixChain]
  | succ l ih =>
    rw [gaussianMatrixChain]
    have hD : (fun i : Fin (l+1+1) =>
        (Fin.cons D0 D : Fin (l+1+1+1) → Matrix (Fin d) (Fin d) ℝ) i.castSucc) =
        (Fin.cons D0 (fun i : Fin (l+1) => D i.castSucc) :
          Fin (l+1+1) → Matrix (Fin d) (Fin d) ℝ) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    have hG : (fun i : Fin (l+1) =>
        (Fin.cons G0 G : Fin (l+1+1) → Matrix (Fin d) (Fin d) ℝ) i.castSucc) =
        (Fin.cons G0 (fun i : Fin l => G i.castSucc) :
          Fin (l+1) → Matrix (Fin d) (Fin d) ℝ) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    rw [hD, hG, ih]
    simp only [gaussianMatrixChain, Fin.cons_last]
    simp only [mul_assoc]

#print axioms gaussianMatrixChain_cons
end SpectralRadiusUpperTail
