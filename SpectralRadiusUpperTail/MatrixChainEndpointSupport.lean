import SpectralRadiusUpperTail.MatrixChainProjectionCancel
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- A projected first bridge leaves a nonempty chain supported at its
initial coordinate. -/
theorem matrixChain_projection_left_support (d l : ℕ)
    (P C : Fin (l+1+1) → Matrix (Fin d) (Fin d) ℝ)
    (G : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ)
    (h : P 0 * C 0 * P 0 = C 0 * P 0) :
    P 0 * gaussianMatrixChain d (l+1) C
        (fun j => P j.castSucc * G j * P j.succ) =
    gaussianMatrixChain d (l+1) C
      (fun j => P j.castSucc * G j * P j.succ) := by
  let Ct : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ := fun i => C i.succ
  let Gt : Fin l → Matrix (Fin d) (Fin d) ℝ := fun j => G j.succ
  have hC : C = Fin.cons (C 0) Ct := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hG :
      (fun j : Fin (l+1) => P j.castSucc * G j * P j.succ) =
      Fin.cons (P 0 * G 0 * P (Fin.succ 0))
        (fun j : Fin l => P j.succ.castSucc * Gt j * P j.succ.succ) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  rw [hC, hG, gaussianMatrixChain_cons]
  calc
    P 0 * (C 0 * (P 0 * G 0 * P (Fin.succ 0)) *
      gaussianMatrixChain d l Ct
        (fun j => P j.succ.castSucc * Gt j * P j.succ.succ)) =
      (P 0 * C 0 * P 0) * G 0 * P (Fin.succ 0) *
        gaussianMatrixChain d l Ct
          (fun j => P j.succ.castSucc * Gt j * P j.succ.succ) := by
      simp only [mul_assoc]
    _ = (C 0 * P 0) * G 0 * P (Fin.succ 0) *
        gaussianMatrixChain d l Ct
          (fun j => P j.succ.castSucc * Gt j * P j.succ.succ) := by rw [h]
    _ = C 0 * (P 0 * G 0 * P (Fin.succ 0)) *
        gaussianMatrixChain d l Ct
          (fun j => P j.succ.castSucc * Gt j * P j.succ.succ) := by
      simp only [mul_assoc]

/-- A projected final bridge leaves a chain supported at its terminal
coordinate, even when the final diagonal waiting exponent is zero. -/
theorem matrixChain_projection_right_support (d l : ℕ)
    (P C : Fin (l+1+1) → Matrix (Fin d) (Fin d) ℝ)
    (G : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ)
    (h : P (Fin.last (l+1)) * C (Fin.last (l+1)) *
        P (Fin.last (l+1)) =
      P (Fin.last (l+1)) * C (Fin.last (l+1))) :
    gaussianMatrixChain d (l+1) C
        (fun j => P j.castSucc * G j * P j.succ) *
      P (Fin.last (l+1)) =
    gaussianMatrixChain d (l+1) C
      (fun j => P j.castSucc * G j * P j.succ) := by
  let F := gaussianMatrixChain d l
    (fun i => C i.castSucc)
    (fun i => P i.castSucc.castSucc * G i.castSucc * P i.castSucc.succ)
  let H := P (Fin.last l).castSucc * G (Fin.last l)
  let Q := P (Fin.last (l+1))
  have hq : P (Fin.last l).succ = Q := by rfl
  change ((F * (H * Q)) * C (Fin.last (l+1))) * Q =
    (F * (H * Q)) * C (Fin.last (l+1))
  calc
    _ = F * H * (Q * C (Fin.last (l+1)) * Q) := by
      simp only [mul_assoc]
    _ = F * H * (Q * C (Fin.last (l+1))) := by rw [h]
    _ = _ := by simp only [mul_assoc]

#print axioms matrixChain_projection_left_support
#print axioms matrixChain_projection_right_support
end SpectralRadiusUpperTail
