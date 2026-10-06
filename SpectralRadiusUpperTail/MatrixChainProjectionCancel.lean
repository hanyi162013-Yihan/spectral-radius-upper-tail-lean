import SpectralRadiusUpperTail.SchurMatrixChainCons
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The support projections on Gaussian bridges disappear between the
supported diagonal factors of a matrix chain. -/
theorem matrixChain_projection_cancel (d : ℕ) :
    ∀ l : ℕ,
      ∀ (P C A : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ)
        (G : Fin l → Matrix (Fin d) (Fin d) ℝ),
      (∀ i, P i * C i * P i = A i) →
      P 0 * gaussianMatrixChain d l C
          (fun j => P j.castSucc * G j * P j.succ) * P (Fin.last l) =
        gaussianMatrixChain d l A G := by
  intro l
  induction l with
  | zero =>
    intro P C A G h
    simpa only [gaussianMatrixChain, Fin.last_zero, Fin.zero_eta] using h 0
  | succ l ih =>
    intro P C A G h
    let Pt : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ := fun i => P i.succ
    let Ct : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ := fun i => C i.succ
    let At : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ := fun i => A i.succ
    let Gt : Fin l → Matrix (Fin d) (Fin d) ℝ := fun j => G j.succ
    have htail : ∀ i, Pt i * Ct i * Pt i = At i := by
      intro i
      exact h i.succ
    have hchain := ih Pt Ct At Gt htail
    have hP : P = Fin.cons (P 0) Pt := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hC : C = Fin.cons (C 0) Ct := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hA : A = Fin.cons (A 0) At := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hG : G = Fin.cons (G 0) Gt := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hhead : P 0 * C 0 * P 0 = A 0 := h 0
    rw [hP, hC, hA, hG]
    simp only [Fin.cons_zero, Fin.cons_last]
    have hbridge :
        (fun j : Fin (l+1) =>
          (Fin.cons (P 0) Pt : Fin (l+1+1) → Matrix (Fin d) (Fin d) ℝ) j.castSucc *
            (Fin.cons (G 0) Gt : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ) j *
            (Fin.cons (P 0) Pt : Fin (l+1+1) → Matrix (Fin d) (Fin d) ℝ) j.succ) =
        Fin.cons (P 0 * G 0 * Pt 0)
          (fun j : Fin l => Pt j.castSucc * Gt j * Pt j.succ) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> rfl
    rw [hbridge, gaussianMatrixChain_cons, gaussianMatrixChain_cons]
    calc
      (P 0 * (C 0 * (P 0 * G 0 * Pt 0) *
          gaussianMatrixChain d l Ct
            (fun j => Pt j.castSucc * Gt j * Pt j.succ))) * Pt (Fin.last l) =
          (P 0 * C 0 * P 0) * G 0 *
            ((Pt 0 * gaussianMatrixChain d l Ct
              (fun j => Pt j.castSucc * Gt j * Pt j.succ)) * Pt (Fin.last l)) := by
        simp only [mul_assoc]
      _ = A 0 * G 0 * gaussianMatrixChain d l At Gt := by
        rw [hhead, hchain]

#print axioms matrixChain_projection_cancel
end SpectralRadiusUpperTail
