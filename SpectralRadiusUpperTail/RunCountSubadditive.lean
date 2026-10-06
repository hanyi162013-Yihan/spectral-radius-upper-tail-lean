import SpectralRadiusUpperTail.SignRunCount

namespace SpectralRadiusUpperTail
variable {A : Type*} [DecidableEq A]

lemma signRunCount_append_le (l k : List A) :
    signRunCount (l++k) ≤ signRunCount l + signRunCount k := by
  induction l with
  | nil => simp [signRunCount]
  | cons a l ih =>
    cases l with
    | nil =>
      simpa only [List.singleton_append,signRunCount,Nat.add_comm] using (signRunCount_cons_bounds a k).2
    | cons b l =>
      simp only [List.cons_append,signRunCount] at ih ⊢
      split_ifs <;> omega

lemma signRunCount_replicate_le (n : ℕ) (a : A) : signRunCount (List.replicate n a) ≤ 1 := by
  induction n with
  | zero => simp [signRunCount]
  | succ n ih =>
    cases n with
    | zero => simp [signRunCount]
    | succ n => simpa only [List.replicate_succ,signRunCount,if_true,Nat.add_zero] using ih

lemma signRunCount_flatten_le (C : List (List A)) :
    signRunCount C.flatten ≤ (C.map signRunCount).sum := by
  induction C with
  | nil => simp [signRunCount]
  | cons c C ih =>
    simpa only [List.flatten_cons,List.map_cons,List.sum_cons] using
      Nat.le_trans (signRunCount_append_le c C.flatten) (Nat.add_le_add_left ih _)

lemma signRunCount_uniform_blocks_le (labels : List A) (m : ℕ) :
    signRunCount (labels.flatMap (List.replicate m)) ≤ labels.length := by
  induction labels with
  | nil => simp [signRunCount]
  | cons a labels ih =>
    simp only [List.flatMap_cons,List.length_cons]
    have h := signRunCount_append_le (List.replicate m a) (labels.flatMap (List.replicate m))
    have hr := signRunCount_replicate_le m a
    omega

#print axioms signRunCount_append_le
#print axioms signRunCount_replicate_le
#print axioms signRunCount_flatten_le
#print axioms signRunCount_uniform_blocks_le
end SpectralRadiusUpperTail
