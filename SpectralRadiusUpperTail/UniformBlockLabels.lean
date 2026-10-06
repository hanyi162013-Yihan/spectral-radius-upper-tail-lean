import SpectralRadiusUpperTail.UniformBlockIndex
import SpectralRadiusUpperTail.RunCountSubadditive
import SpectralRadiusUpperTail.FiniteWordListCount

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Original block identity, independent of whether two blocks have the same sign. -/
def uniformBlockLabel {B m : ℕ} (i : Fin (B*m)) : Fin B := (finProdFinEquiv.symm i).1

lemma uniformBlockLabel_index {B m : ℕ} (b : Fin B) (j : Fin m) :
    uniformBlockLabel (uniformBlockIndex b j) = b := by
  exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (b,j))

lemma uniformBlockLabel_rows (B m : ℕ) :
    List.ofFn (@uniformBlockLabel B m) =
      (List.ofFn (fun b : Fin B => b)).flatMap (List.replicate m) := by
  rw [List.ofFn_mul]
  have h (b : Fin B) (j : Fin m) (hij : b.val*m+j.val < B*m) :
      uniformBlockLabel (⟨b.val*m+j.val,hij⟩ : Fin (B*m)) = b := by
    have he : (⟨b.val*m+j.val,hij⟩ : Fin (B*m)) = uniformBlockIndex b j := by
      apply Fin.ext
      change b.val*m+j.val = j.val+m*b.val
      ac_rfl
    rw [he,uniformBlockLabel_index]
  simp only [h,List.ofFn_const,List.flatMap_def,List.map_ofFn,Function.comp_def]

lemma uniformBlockLabel_run_budget (B m : ℕ) :
    signRunCount (List.ofFn (@uniformBlockLabel B m)) ≤ B := by
  rw [uniformBlockLabel_rows]
  simpa only [List.length_ofFn] using
    signRunCount_uniform_blocks_le (List.ofFn (fun b : Fin B => b)) m

lemma uniformBlockLabel_count (B m : ℕ) (b : Fin B) :
    (List.ofFn (@uniformBlockLabel B m)).count b = m := by
  rw [uniformBlockLabel_rows,List.count_flatMap]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def,List.count_replicate,beq_iff_eq]
  simp

#print axioms uniformBlockLabel
#print axioms uniformBlockLabel_index
#print axioms uniformBlockLabel_rows
#print axioms uniformBlockLabel_run_budget
#print axioms uniformBlockLabel_count
end SpectralRadiusUpperTail
