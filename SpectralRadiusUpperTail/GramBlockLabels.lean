import SpectralRadiusUpperTail.UniformBlockLabels
import SpectralRadiusUpperTail.GramTreeSignCast

namespace SpectralRadiusUpperTail

def gramTreeBlock (m q : ℕ) (i : Fin (2*(q*m))) : Fin (2*q) :=
  uniformBlockLabel (Fin.cast (Nat.mul_assoc 2 q m).symm i)

lemma ofFn_precomp_cast {A : Type*} {n k : ℕ} (h : n = k) (f : Fin k → A) :
    List.ofFn (fun i : Fin n => f (Fin.cast h i)) = List.ofFn f := by
  subst k
  rfl

lemma gramTreeBlock_run_budget (m q : ℕ) :
    signRunCount (List.ofFn (gramTreeBlock m q)) ≤ 2*q := by
  unfold gramTreeBlock
  rw [ofFn_precomp_cast]
  exact uniformBlockLabel_run_budget (2*q) m

lemma gramTreeBlock_count (m q : ℕ) (b : Fin (2*q)) :
    (List.ofFn (gramTreeBlock m q)).count b = m := by
  unfold gramTreeBlock
  rw [ofFn_precomp_cast]
  exact uniformBlockLabel_count (2*q) m b

lemma gramTreeBlock_same_sign (m q : ℕ) (i j : Fin (2*(q*m)))
    (h : gramTreeBlock m q i = gramTreeBlock m q j) : gramTreeSign m q i = gramTreeSign m q j := by
  let x := Fin.cast (Nat.mul_assoc 2 q m).symm i
  let y := Fin.cast (Nat.mul_assoc 2 q m).symm j
  obtain ⟨b,a,hx⟩ := uniformBlockIndex_cover (2*q) m x
  obtain ⟨c,d,hy⟩ := uniformBlockIndex_cover (2*q) m y
  have hb : b = c := by
    change uniformBlockLabel x = uniformBlockLabel y at h
    rw [← hx,← hy,uniformBlockLabel_index,uniformBlockLabel_index] at h
    exact h
  subst c
  change gramFiniteSign m q x = gramFiniteSign m q y
  rw [← hx,← hy]
  exact gramFiniteSign_block_constant m q b a d

#print axioms gramTreeBlock
#print axioms ofFn_precomp_cast
#print axioms gramTreeBlock_run_budget
#print axioms gramTreeBlock_count
#print axioms gramTreeBlock_same_sign
end SpectralRadiusUpperTail
