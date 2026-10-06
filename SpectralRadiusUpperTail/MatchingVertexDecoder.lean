import SpectralRadiusUpperTail.BoolPathEquality
import Mathlib.Data.Setoid.Basic

namespace SpectralRadiusUpperTail

def boolFlipTrace (flip : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k+1 => Bool.xor (boolFlipTrace flip k) (flip k)

lemma boolFlipTrace_step (flip : ℕ → Bool) (k : ℕ) :
    boolFlipTrace flip k = boolFlipTrace flip (k+1) ↔ flip k = false := by
  rw [boolFlipTrace]
  cases boolFlipTrace flip k <;> cases flip k <;> decide

/-- A purely combinatorial cut color, initialized at false and flipped at the
two occurrences paired by f. It uses no ambient vertex or entry labels. -/
def matchingVertexColor {n : ℕ} (f : Fin n → Fin n) (i : Fin n)
    (a : Fin (n+1)) : Bool :=
  boolFlipTrace (fun k => decide (k = i.val ∨ k = (f i).val)) a.val

lemma matchingVertexColor_step {n : ℕ} (f : Fin n → Fin n) (i j : Fin n) :
    matchingVertexColor f i j.castSucc = matchingVertexColor f i j.succ ↔
      ¬ (j = i ∨ j = f i) := by
  unfold matchingVertexColor
  simp only [Fin.val_castSucc,Fin.val_succ,boolFlipTrace_step,decide_eq_false_iff_not,Fin.ext_iff]

def matchingVertexSetoid {n : ℕ} (f : Fin n → Fin n) : Setoid (Fin (n+1)) :=
  Setoid.ker (fun a => fun i : Fin n => matchingVertexColor f i a)

lemma matchingVertexSetoid_iff {n : ℕ} (f : Fin n → Fin n) (a b : Fin (n+1)) :
    matchingVertexSetoid f a b ↔ ∀ i, matchingVertexColor f i a = matchingVertexColor f i b := by
  change (fun i => matchingVertexColor f i a) = (fun i => matchingVertexColor f i b) ↔ _
  exact funext_iff

#print axioms boolFlipTrace
#print axioms boolFlipTrace_step
#print axioms matchingVertexColor
#print axioms matchingVertexColor_step
#print axioms matchingVertexSetoid
#print axioms matchingVertexSetoid_iff
end SpectralRadiusUpperTail
