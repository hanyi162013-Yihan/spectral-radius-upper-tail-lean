import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

namespace SpectralRadiusUpperTail
variable {A : Type*}

/-- End markers encode boundaries without empty chunks. -/
def markChunkEnd : List A → List (A × Bool)
  | [] => []
  | [a] => [(a,true)]
  | a::b::l => (a,false)::markChunkEnd (b::l)

def markChunkEnds (C : List (List A)) : List (A × Bool) := C.flatMap markChunkEnd

def decodeChunkEnds : List (A × Bool) → List (List A)
  | [] => []
  | (a,b)::l =>
    if b then [a]::decodeChunkEnds l
    else match decodeChunkEnds l with
      | [] => [[a]]
      | k::K => (a::k)::K

lemma markChunkEnd_length (l : List A) : (markChunkEnd l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => simpa only [markChunkEnd,List.length_cons] using congrArg Nat.succ ih

lemma markChunkEnds_length (C : List (List A)) :
    (markChunkEnds C).length = C.flatten.length := by
  simp only [markChunkEnds,List.length_flatMap,markChunkEnd_length,List.length_flatten]

lemma decodeChunkEnd_append (l : List A) (hl : l ≠ []) (tail : List (A × Bool)) :
    decodeChunkEnds (markChunkEnd l ++ tail) = l :: decodeChunkEnds tail := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons a l ih =>
    cases l with
    | nil => simp [markChunkEnd,decodeChunkEnds]
    | cons b l =>
      have h := ih (by simp)
      simp only [markChunkEnd,List.cons_append,decodeChunkEnds,Bool.false_eq_true,if_false,h]

lemma decode_markChunkEnds (C : List (List A)) (h : ∀ l ∈ C, l ≠ []) :
    decodeChunkEnds (markChunkEnds C) = C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    have hl := h l (by simp)
    have hC : ∀ k ∈ C, k ≠ [] := fun k hk => h k (List.mem_cons_of_mem l hk)
    change decodeChunkEnds (markChunkEnd l ++ markChunkEnds C) = l::C
    rw [decodeChunkEnd_append l hl,ih hC]

lemma markChunkEnds_injective {C D : List (List A)}
    (hC : ∀ l ∈ C, l ≠ []) (hD : ∀ l ∈ D, l ≠ [])
    (h : markChunkEnds C = markChunkEnds D) : C = D := by
  have hd := congrArg decodeChunkEnds h
  simpa only [decode_markChunkEnds C hC,decode_markChunkEnds D hD] using hd

#print axioms markChunkEnd
#print axioms markChunkEnds
#print axioms decodeChunkEnds
#print axioms markChunkEnd_length
#print axioms markChunkEnds_length
#print axioms decodeChunkEnd_append
#print axioms decode_markChunkEnds
#print axioms markChunkEnds_injective
end SpectralRadiusUpperTail
