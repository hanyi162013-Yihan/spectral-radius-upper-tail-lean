import SpectralRadiusUpperTail.MatrixWordWalkProduct

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {α ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

def matrixMappedWalkTerm (f : α → Matrix ι ι R) (L : List α)
    (q : ι → R) (i : ι) (v : Fin L.length → ι) : R :=
  matrixWordWalkTerm q (L.map f) i (fun a => v (Fin.cast (List.length_map (f := f)) a))

lemma matrixMappedWalkTerm_product (f : α → Matrix ι ι R) (L : List α)
    (q : ι → R) (i : ι) (v : Fin L.length → ι) :
    matrixMappedWalkTerm f L q i v =
      (∏ a : Fin L.length, f (L.get a)
        ((Fin.cons i v : Fin (L.length+1) → ι) a.castSucc)
        ((Fin.cons i v : Fin (L.length+1) → ι) a.succ)) *
      q ((Fin.cons i v : Fin (L.length+1) → ι) (Fin.last L.length)) := by
  induction L generalizing i with
  | nil => simp [matrixMappedWalkTerm, List.map_nil, matrixWordWalkTerm] <;> rfl
  | cons a L ih =>
    have hs : matrixMappedWalkTerm f (a::L) q i v =
        f a i (v 0) * matrixMappedWalkTerm f L q (v 0) (fun j => v j.succ) := rfl
    have hv : (Fin.cons (v 0) (fun j : Fin L.length => v j.succ) :
        Fin (L.length+1) → ι) = v := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have hl : Fin.last (L.length+1) = (Fin.last L.length).succ := rfl
    rw [hs, ih]
    simp only [List.length_cons] at *
    rw [Fin.prod_univ_succ]
    simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
      Fin.castSucc_succ, hv, hl, List.get_cons_zero]
    rw [mul_assoc]
    rfl

#print axioms matrixMappedWalkTerm
#print axioms matrixMappedWalkTerm_product
end SpectralRadiusUpperTail
