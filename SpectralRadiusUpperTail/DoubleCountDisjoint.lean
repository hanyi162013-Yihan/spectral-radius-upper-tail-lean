import SpectralRadiusUpperTail.UniqueDoubleEntryTour

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {I A : Type*} [Fintype I] [DecidableEq A] [BEq A] [LawfulBEq A]

/-- A total count at most two forces two-count supports in different indexed
pieces to be disjoint. No disjointness of their vertex sets is asserted. -/
lemma doubleCount_supports_disjoint (words : I → List A) (S : I → Finset A)
    (hlocal : ∀ i a, a ∈ S i → (words i).count a = 2)
    (htotal : ∀ a, ∑ i, (words i).count a ≤ 2) : Pairwise (fun i j => Disjoint (S i) (S j)) := by
  classical
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro a hai haj
  have hle : (∑ k ∈ ({i,j} : Finset I), (words k).count a) ≤
      ∑ k, (words k).count a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
  rw [Finset.sum_pair hij,hlocal i a hai,hlocal j a haj] at hle
  have hh := htotal a
  omega

lemma list_indexed_count_sum (L : List (List A)) (a : A) :
    (∑ i : Fin L.length, (L.get i).count a) = L.flatten.count a := by
  have hh := congrArg (fun J : List (List A) => (J.map (fun w => w.count a)).sum)
    (List.ofFn_get L)
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def] at hh
  rw [hh]
  simpa only [List.flatMap_id,Function.comp_def,id_eq] using (List.count_flatMap (f := id) (l := L) (x := a)).symm

#print axioms doubleCount_supports_disjoint
#print axioms list_indexed_count_sum
end SpectralRadiusUpperTail
