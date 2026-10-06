import SpectralRadiusUpperTail.SchurMatrixChainCons

namespace SpectralRadiusUpperTail

/-- One block-chain term with prescribed strict vertices and diagonal
waiting times. Strictness is imposed on the path when summing these terms. -/
noncomputable def schurStrictPathTerm (d N l : ℕ)
    (D : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin N) (Fin N) (Matrix (Fin d) (Fin d) ℝ))
    (p : Fin (l+1) → Fin N) (m : Fin (l+1) → ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  gaussianMatrixChain d l (fun j => (D (p j))^(m j))
    (fun j => U (p j.castSucc) (p j.succ))

/-- Deleting the first edge of a block chain leaves a smaller chain,
with the matrix factors in their original noncommutative order. -/
theorem schurStrictPathTerm_cons (d N l : ℕ)
    (D : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin N) (Fin N) (Matrix (Fin d) (Fin d) ℝ))
    (i : Fin N) (q : Fin (l+1) → Fin N)
    (s : ℕ) (t : Fin (l+1) → ℕ) :
    schurStrictPathTerm d N (l+1) D U (Fin.cons i q) (Fin.cons s t) =
      (D i)^s * U i (q 0) * schurStrictPathTerm d N l D U q t := by
  have hD :
      (fun j : Fin (l+1+1) =>
        (D ((Fin.cons i q : Fin (l+1+1) → Fin N) j))^
          ((Fin.cons s t : Fin (l+1+1) → ℕ) j)) =
      Fin.cons ((D i)^s) (fun j : Fin (l+1) => (D (q j))^(t j)) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  have hU :
      (fun j : Fin (l+1) =>
        U ((Fin.cons i q : Fin (l+1+1) → Fin N) j.castSucc)
          ((Fin.cons i q : Fin (l+1+1) → Fin N) j.succ)) =
      Fin.cons (U i (q 0))
        (fun j : Fin l => U (q j.castSucc) (q j.succ)) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  unfold schurStrictPathTerm
  rw [hD,hU]
  exact gaussianMatrixChain_cons d l ((D i)^s)
    (fun j => (D (q j))^(t j)) (U i (q 0))
    (fun j => U (q j.castSucc) (q j.succ))

#print axioms schurStrictPathTerm_cons
end SpectralRadiusUpperTail
