import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

def uniformBlockIndex {B m : ℕ} (b : Fin B) (j : Fin m) : Fin (B*m) :=
  finProdFinEquiv (b,j)

lemma uniformBlockIndex_cover (B m : ℕ) (t : Fin (B*m)) :
    ∃ b j, uniformBlockIndex b j = t := by
  obtain ⟨⟨b,j⟩,h⟩ := finProdFinEquiv.surjective t
  exact ⟨b,j,h⟩

lemma uniformBlockIndex_strictMono {B m : ℕ} (b : Fin B) :
    StrictMono (uniformBlockIndex (m := m) b) := by
  intro i j hij
  change i.val + m*b.val < j.val + m*b.val
  exact Nat.add_lt_add_right hij _

lemma uniformBlockIndex_convex {B m : ℕ} (b : Fin B) (i j : Fin m)
    (t : Fin (B*m)) (hi : uniformBlockIndex b i ≤ t)
    (hj : t ≤ uniformBlockIndex b j) : ∃ k : Fin m, uniformBlockIndex b k = t := by
  have hival : i.val + m*b.val ≤ t.val := hi
  have hjval : t.val ≤ j.val + m*b.val := hj
  have hjm := j.isLt
  let k : Fin m := ⟨t.val - m*b.val, by omega⟩
  refine ⟨k,?_⟩
  apply Fin.ext
  change (t.val - m*b.val) + m*b.val = t.val
  omega

#print axioms uniformBlockIndex
#print axioms uniformBlockIndex_cover
#print axioms uniformBlockIndex_strictMono
#print axioms uniformBlockIndex_convex
end SpectralRadiusUpperTail
