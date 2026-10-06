import SpectralRadiusUpperTail.MatrixWalkExpansion

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- Each actual walk term is the product of its directed-edge entries and
its terminal vector weight. -/
lemma matrixWalkTerm_product (A : Matrix ι ι R) (q : ι → R) (k : ℕ) (i : ι)
    (v : Fin k → ι) :
    matrixWalkTerm A q k i v =
      (∏ j : Fin k, A ((Fin.cons i v : Fin (k+1) → ι) j.castSucc) ((Fin.cons i v : Fin (k+1) → ι) j.succ))*
        q ((Fin.cons i v : Fin (k+1) → ι) (Fin.last k)) := by
  induction k generalizing i with
  | zero => simp [matrixWalkTerm]
  | succ k ih =>
    have hv : (Fin.cons (v 0) (fun j => v j.succ) : Fin (k+1) → ι) = v := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have hl : Fin.last (k+1) = (Fin.last k).succ := rfl
    rw [matrixWalkTerm, ih, Fin.prod_univ_succ]
    simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_succ,
      hv, hl]
    rw [mul_assoc]

#print axioms matrixWalkTerm_product
end SpectralRadiusUpperTail
