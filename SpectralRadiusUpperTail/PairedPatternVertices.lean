import Mathlib.Data.List.OfFn
import Mathlib.Data.Setoid.Basic

namespace SpectralRadiusUpperTail
variable {k : ℕ}

/-- Left path vertices in a prescribed equality pattern of two paths. -/
def patternLeftVertex (r : Setoid (Fin (k+1) ⊕ Fin (k+1)))
    (a : Fin (k+1)) : Quotient r := Quotient.mk r (Sum.inl a)

/-- Right path vertices in the same quotient. -/
def patternRightVertex (r : Setoid (Fin (k+1) ⊕ Fin (k+1)))
    (a : Fin (k+1)) : Quotient r := Quotient.mk r (Sum.inr a)

/-- The canonical quotient paths cover every vertex of the quotient type. -/
lemma pairedPattern_vertex_cover (r : Setoid (Fin (k+1) ⊕ Fin (k+1)))
    (x : Quotient r) :
    x ∈ patternLeftVertex r 0 :: List.ofFn (fun a : Fin k => patternLeftVertex r a.succ) ∨
      x ∈ patternRightVertex r 0 :: List.ofFn (fun a : Fin k => patternRightVertex r a.succ) := by
  induction x using Quotient.inductionOn with
  | _ x =>
    cases x with
    | inl a =>
      left
      refine Fin.cases ?_ (fun b => ?_) a
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨b,rfl⟩)
    | inr a =>
      right
      refine Fin.cases ?_ (fun b => ?_) a
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨b,rfl⟩)

/-- Assigning labels to quotient vertices recovers the corresponding left
 and right coordinate labels exactly. -/
lemma pairedPattern_label_factorization {β : Type*}
    (x : (Fin (k+1) ⊕ Fin (k+1)) → β) (a : Fin (k+1)) :
    Setoid.kerLift x (patternLeftVertex (Setoid.ker x) a) = x (Sum.inl a) ∧
      Setoid.kerLift x (patternRightVertex (Setoid.ker x) a) = x (Sum.inr a) := ⟨rfl,rfl⟩

#print axioms patternLeftVertex
#print axioms patternRightVertex
#print axioms pairedPattern_vertex_cover
#print axioms pairedPattern_label_factorization
end SpectralRadiusUpperTail
