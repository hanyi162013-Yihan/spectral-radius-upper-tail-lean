import SpectralRadiusUpperTail.MatrixSignedWord
import Mathlib.Data.List.GetD
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

lemma gramSignWord_succ (m q : ℕ) :
    gramSignWord m (q+1) = (List.replicate m false ++ List.replicate m true) ++
      gramSignWord m q := by
  simp only [gramSignWord, List.replicate_succ, List.flatten_cons]

/-- The actual Gram sign list is constant on every length-m block. -/
lemma gramSignWord_block_constant (m q b i j : ℕ) (hb : b < 2*q)
    (hi : i < m) (hj : j < m) :
    (gramSignWord m q).getD (m*b+i) false =
      (gramSignWord m q).getD (m*b+j) false := by
  induction q generalizing b with
  | zero => omega
  | succ q ih =>
    rw [gramSignWord_succ]
    by_cases hb0 : b = 0
    · subst b
      simp only [Nat.mul_zero, Nat.zero_add]
      rw [List.getD_append (List.replicate m false ++ List.replicate m true) (gramSignWord m q) false _ (by simp only [List.length_append, List.length_replicate]; omega),
        List.getD_append (List.replicate m false ++ List.replicate m true) (gramSignWord m q) false _ (by simp only [List.length_append, List.length_replicate]; omega)]
      rw [List.getD_append _ _ _ _ (by simpa using hi),
        List.getD_append _ _ _ _ (by simpa using hj)]
      rw [List.getD_replicate _ hi, List.getD_replicate _ hj]
    · by_cases hb1 : b = 1
      · subst b
        simp only [Nat.mul_one]
        rw [List.getD_append (List.replicate m false ++ List.replicate m true) (gramSignWord m q) false _ (by simp only [List.length_append, List.length_replicate]; omega),
          List.getD_append (List.replicate m false ++ List.replicate m true) (gramSignWord m q) false _ (by simp only [List.length_append, List.length_replicate]; omega)]
        rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega),
          List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
        simp only [List.length_replicate, Nat.add_sub_cancel_left]
        rw [List.getD_replicate _ hi, List.getD_replicate _ hj]
      · have he : m*b = m*(b-2)+(m+m) := by
          have hbe : b = (b-2)+2 := by omega
          calc m*b = m*((b-2)+2) := congrArg (m*·) hbe
               _ = m*(b-2)+(m+m) := by ring
        rw [List.getD_append_right (List.replicate m false ++ List.replicate m true) (gramSignWord m q) false _ (by simp only [List.length_append, List.length_replicate]; omega),
          List.getD_append_right (List.replicate m false ++ List.replicate m true) (gramSignWord m q) false _ (by simp only [List.length_append, List.length_replicate]; omega)]
        simp only [List.length_append, List.length_replicate]
        have hei : m*b+i-(m+m) = m*(b-2)+i := by omega
        have hej : m*b+j-(m+m) = m*(b-2)+j := by omega
        rw [hei,hej]
        exact ih (b-2) (by omega)

#print axioms gramSignWord_succ
#print axioms gramSignWord_block_constant
end SpectralRadiusUpperTail
