import SpectralRadiusUpperTail.MatrixMappedWalkProduct

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {α ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

lemma matrixMappedWalkTerm_sum (f : α → Matrix ι ι R) (L : List α)
    (q : ι → R) (i : ι) :
    (∑ v : Fin L.length → ι, matrixMappedWalkTerm f L q i v) = (L.map f).prod.mulVec q i := by
  induction L generalizing i with
  | nil => simp [matrixMappedWalkTerm, List.map_nil, matrixWordWalkTerm] <;> rfl
  | cons a L ih =>
    calc
      _ = ∑ z : ι × (Fin L.length → ι),
          matrixMappedWalkTerm f (a::L) q i ((matrixWalkSplit L.length).symm z) :=
        ((matrixWalkSplit L.length).symm.sum_comp _).symm
      _ = ∑ j, ∑ v : Fin L.length → ι,
          f a i j * matrixMappedWalkTerm f L q j v := by
        rw [Fintype.sum_prod_type]
        rfl
      _ = ∑ j, f a i j * (L.map f).prod.mulVec q j := by
        simp only [← Finset.mul_sum, ih]
      _ = _ := by
        rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
        rfl

lemma matrixMapped_trace_walk_sum (f : α → Matrix ι ι R) (L : List α)
    (B : Matrix ι ι R) :
    ((L.map f).prod * B).trace =
      ∑ i, ∑ v : Fin L.length → ι, matrixMappedWalkTerm f L (fun j => B j i) i v := by
  simp_rw [matrixMappedWalkTerm_sum]
  rfl

#print axioms matrixMappedWalkTerm_sum
#print axioms matrixMapped_trace_walk_sum
end SpectralRadiusUpperTail
