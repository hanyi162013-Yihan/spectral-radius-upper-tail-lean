import SpectralRadiusUpperTail.SignRunCount

namespace SpectralRadiusUpperTail
variable {A B : Type*} [DecidableEq B]

def labelConstant (f : A → B) (l : List A) : Prop :=
  ∀ a ∈ l, ∀ b ∈ l, f a = f b

lemma labelConstant_cons (f : A → B) (a : A) (l : List A)
    (hl : labelConstant f l) (ha : ∀ b ∈ l, f a = f b) : labelConstant f (a::l) := by
  intro x hx y hy
  rcases List.mem_cons.mp hx with rfl | hx'
  · rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact ha y hy'
  · rcases List.mem_cons.mp hy with rfl | hy'
    · exact (ha x hx').symm
    · exact hl x hx' y hy'

/-- Every payload list admits actual nonempty constant-label fragments, with
exactly its run count. Labels need not be signs: original block IDs are allowed. -/
lemma exists_constant_run_partition (f : A → B) (l : List A) :
    ∃ C : List (List A), C.flatten = l ∧
      (∀ c ∈ C, c ≠ [] ∧ labelConstant f c) ∧ C.length = signRunCount (l.map f) := by
  induction l with
  | nil => exact ⟨[],rfl,by simp, rfl⟩
  | cons a l ih =>
    cases l with
    | nil =>
      refine ⟨[[a]],rfl,?_,rfl⟩
      intro c hc
      have hc' : c = [a] := by simpa using hc
      subst c
      exact ⟨by simp,by intro x hx y hy; simp only [List.mem_singleton] at hx hy; rw [hx,hy]⟩
    | cons b l =>
      obtain ⟨C,hflat,hC,hlen⟩ := ih
      cases C with
      | nil => simp at hflat
      | cons c C =>
        have hc := hC c (by simp)
        cases c with
        | nil => exact (hc.1 rfl).elim
        | cons x xs =>
          change x :: (xs ++ C.flatten) = b :: l at hflat
          have hxb : x = b := (List.cons.inj hflat).1
          subst x
          by_cases hab : f a = f b
          · refine ⟨(a::b::xs)::C,?_,?_,?_⟩
            · simpa only [List.flatten_cons,List.cons_append] using congrArg (List.cons a) hflat
            · intro c hc'
              rcases List.mem_cons.mp hc' with rfl | hc'
              · exact ⟨by simp,labelConstant_cons f a (b::xs) hc.2
                  (fun y hy => hab.trans (hc.2 b (by simp) y hy))⟩
              · exact hC c (List.mem_cons_of_mem _ hc')
            · simpa only [List.length_cons,List.map_cons,signRunCount,hab,if_true,Nat.add_zero] using hlen
          · refine ⟨[a]::(b::xs)::C,?_,?_,?_⟩
            · simpa only [List.flatten_cons,List.singleton_append,List.cons_append,List.nil_append] using congrArg (List.cons a) hflat
            · intro c hc'
              rcases List.mem_cons.mp hc' with rfl | hc'
              · exact ⟨by simp,by intro x hx y hy; simp only [List.mem_singleton] at hx hy; rw [hx,hy]⟩
              · exact hC c hc'
            · simpa only [List.length_cons,List.map_cons,signRunCount,hab,if_false] using congrArg Nat.succ hlen

#print axioms labelConstant
#print axioms labelConstant_cons
#print axioms exists_constant_run_partition
end SpectralRadiusUpperTail
