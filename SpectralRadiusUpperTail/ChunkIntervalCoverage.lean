import SpectralRadiusUpperTail.ChunkInterval

namespace SpectralRadiusUpperTail
variable {A : Type*}

lemma chunkInterval_cover (C : List (List A)) (t : Fin C.flatten.length) :
    ∃ i j, chunkInterval C i j = t := by
  induction C with
  | nil => exact Fin.elim0 t
  | cons c C ih =>
    have ht : t.val < c.length+C.flatten.length := by
      simpa only [List.flatten_cons,List.length_append] using t.isLt
    by_cases h : t.val < c.length
    · refine ⟨⟨0,by simp⟩,⟨t.val,h⟩,Fin.ext ?_⟩
      simp only [chunkInterval,chunkOffset,List.take_zero,List.flatten_nil,List.length_nil,Nat.zero_add]
    · let u : Fin C.flatten.length := ⟨t.val-c.length,by omega⟩
      obtain ⟨i,j,hij⟩ := ih u
      refine ⟨i.succ,j,Fin.ext ?_⟩
      have hv := congrArg Fin.val hij
      change chunkOffset C i+j.val = t.val-c.length at hv
      change chunkOffset (c::C) i.succ+j.val = t.val
      simp only [chunkOffset,Fin.val_succ,List.take_succ_cons,List.flatten_cons,List.length_append]
      change (c.length+chunkOffset C i)+j.val = t.val
      omega

lemma chunkInterval_get (C : List (List A)) (i : Fin C.length) (j : Fin (C.get i).length) :
    C.flatten.get (chunkInterval C i j) = (C.get i).get j := by
  have hbound : chunkOffset C i+j.val < C.flatten.length := (chunkInterval C i j).isLt
  change C.flatten[chunkOffset C i+j.val]'hbound = (C.get i)[j.val]
  have hj := j.isLt
  have hlow : ¬ chunkOffset C i+j.val < (C.take i.val).flatten.length := by
    unfold chunkOffset
    omega
  have hhigh : chunkOffset C i+j.val < (C.take i.val).flatten.length+(C.get i).length := by
    unfold chunkOffset
    omega
  simp only [chunk_middle_decomposition C i]
  simp only [List.getElem_append,List.length_append,hlow,hhigh,dif_neg,dif_pos]
  simp [chunkOffset,Nat.add_sub_cancel_left]

#print axioms chunkInterval_cover
#print axioms chunkInterval_get
end SpectralRadiusUpperTail
