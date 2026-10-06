import SpectralRadiusUpperTail.ConstantRunPartition
import SpectralRadiusUpperTail.IndexedFragmentRunBudget

namespace SpectralRadiusUpperTail
variable {A B : Type*} [DecidableEq B]

/-- Split every surviving segment into actual original-block fragments. The
sum of fragment counts equals the already bounded sum of segment run counts. -/
lemma exists_chunk_run_partitions (f : A → B) (C : List (List A)) :
    ∃ P : List (List (List A)),
      P.map List.flatten = C ∧
      (∀ p ∈ P, ∀ w ∈ p, w ≠ [] ∧ labelConstant f w) ∧
      P.flatten.length = (C.map (fun c => signRunCount (c.map f))).sum := by
  induction C with
  | nil => exact ⟨[],rfl,by simp,rfl⟩
  | cons c C ih =>
    obtain ⟨p,hp,hconst,hnum⟩ := exists_constant_run_partition f c
    obtain ⟨P,hP,hall,hcount⟩ := ih
    refine ⟨p::P,?_,?_,?_⟩
    · simp only [List.map_cons,hp,hP]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hconst
      · exact hall q hq
    · simp only [List.flatten_cons,List.length_append,List.map_cons,List.sum_cons,hnum,hcount]

lemma chunk_run_partitions_budget (f : A → B) (l : List A) (C : List (List A))
    (hsub : C.flatten.Sublist l) (N S : ℕ)
    (hN : signRunCount (l.map f) ≤ N) (hS : C.length ≤ S) :
    ∃ P : List (List (List A)), P.map List.flatten = C ∧
      (∀ p ∈ P, ∀ w ∈ p, w ≠ [] ∧ labelConstant f w) ∧ P.flatten.length ≤ N+(S-1) := by
  obtain ⟨P,hP,hall,hcount⟩ := exists_chunk_run_partitions f C
  exact ⟨P,hP,hall,hcount.le.trans (mapped_sublist_chunk_run_budget f l C hsub N S hN hS)⟩

#print axioms exists_chunk_run_partitions
#print axioms chunk_run_partitions_budget
end SpectralRadiusUpperTail
