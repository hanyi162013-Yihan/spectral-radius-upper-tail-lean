import Mathlib.Data.List.Flatten
import Mathlib.Data.List.TakeDrop
import Mathlib.Order.Fin.Basic
import Lean.Elab.Tactic.Omega

namespace SpectralRadiusUpperTail
variable {A : Type*}

def chunkOffset (C : List (List A)) (i : Fin C.length) : ℕ := (C.take i.val).flatten.length

lemma chunk_middle_decomposition (C : List (List A)) (i : Fin C.length) :
    C.flatten = (C.take i.val).flatten ++ (C.get i) ++ (C.drop (i.val+1)).flatten := by
  have h := congrArg List.flatten (List.take_append_drop (i.val+1) C)
  rw [List.take_succ_eq_append_getElem i.isLt] at h
  simpa only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,
    List.get_eq_getElem] using h.symm

lemma chunkOffset_length_le (C : List (List A)) (i : Fin C.length) :
    chunkOffset C i + (C.get i).length ≤ C.flatten.length := by
  have h := congrArg List.length (chunk_middle_decomposition C i)
  simp only [List.length_append] at h
  unfold chunkOffset
  omega

/-- The actual contiguous embedding of the i-th fragment into the joined word. -/
def chunkInterval (C : List (List A)) (i : Fin C.length) (j : Fin (C.get i).length) :
    Fin C.flatten.length :=
  ⟨chunkOffset C i+j.val,by have h := chunkOffset_length_le C i; have hj := j.isLt; omega⟩

lemma chunkInterval_strictMono (C : List (List A)) (i : Fin C.length) :
    StrictMono (chunkInterval C i) := by
  intro a b hab
  change chunkOffset C i+a.val < chunkOffset C i+b.val
  exact Nat.add_lt_add_left hab _

lemma chunkInterval_convex (C : List (List A)) (i : Fin C.length)
    (a b : Fin (C.get i).length) (t : Fin C.flatten.length)
    (ha : chunkInterval C i a ≤ t) (hb : t ≤ chunkInterval C i b) :
    ∃ j, chunkInterval C i j = t := by
  have ha' : chunkOffset C i+a.val ≤ t.val := ha
  have hb' : t.val ≤ chunkOffset C i+b.val := hb
  let j : Fin (C.get i).length := ⟨t.val-chunkOffset C i,by have hh := b.isLt; omega⟩
  refine ⟨j,Fin.ext ?_⟩
  change chunkOffset C i+(t.val-chunkOffset C i) = t.val
  omega

#print axioms chunkOffset
#print axioms chunk_middle_decomposition
#print axioms chunkOffset_length_le
#print axioms chunkInterval
#print axioms chunkInterval_strictMono
#print axioms chunkInterval_convex
end SpectralRadiusUpperTail
