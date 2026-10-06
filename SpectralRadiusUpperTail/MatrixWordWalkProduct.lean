import SpectralRadiusUpperTail.MatrixWordWalkExpansion

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

lemma matrixWordWalkTerm_product (L : List (Matrix ι ι R)) (q : ι → R)
    (i : ι) (v : Fin L.length → ι) :
    matrixWordWalkTerm q L i v =
      (∏ a : Fin L.length, (L.get a)
        ((Fin.cons i v : Fin (L.length+1) → ι) a.castSucc)
        ((Fin.cons i v : Fin (L.length+1) → ι) a.succ)) *
      q ((Fin.cons i v : Fin (L.length+1) → ι) (Fin.last L.length)) := by
  induction L generalizing i with
  | nil => simp [matrixWordWalkTerm]
  | cons A L ih =>
    have hv : (Fin.cons (v 0) (fun j : Fin L.length => v j.succ) :
        Fin (L.length+1) → ι) = v := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have hl : Fin.last (L.length+1) = (Fin.last L.length).succ := rfl
    simp only [matrixWordWalkTerm, ih]
    simp only [List.length_cons] at *
    rw [Fin.prod_univ_succ]
    simp only [List.length_cons, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
      Fin.castSucc_succ, hv, hl, List.get_cons_zero, List.get_cons_succ]
    rw [mul_assoc]
    rfl

#print axioms matrixWordWalkTerm_product
end SpectralRadiusUpperTail
