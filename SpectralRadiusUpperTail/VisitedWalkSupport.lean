import SpectralRadiusUpperTail.AmbientTreeMatching
import Mathlib.Data.Fintype.Quotient

namespace SpectralRadiusUpperTail
variable {V W : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

/-- Restrict a path's vertex type to exactly the vertices it visits. -/
def visitedWalkPath (p : Fin (n+1) → V) (i : Fin (n+1)) : Set.range p :=
  ⟨p i, ⟨i,rfl⟩⟩

lemma visitedWalkPath_surjective (p : Fin (n+1) → V) :
    Function.Surjective (visitedWalkPath p) := by
  rintro ⟨x,i,rfl⟩
  exact ⟨i,rfl⟩

lemma orientedWalkEdge_comp (s : Fin n → Bool) (p : Fin (n+1) → V)
    (f : V → W) (i : Fin n) :
    orientedWalkEdge s (f ∘ p) i = Prod.map f f (orientedWalkEdge s p i) := by
  cases h : s i <;> simp [orientedWalkEdge,h]

lemma visitedWalkEdge_val (s : Fin n → Bool) (p : Fin (n+1) → V) (i : Fin n) :
    Prod.map Subtype.val Subtype.val (orientedWalkEdge s (visitedWalkPath p) i) =
      orientedWalkEdge s p i := by
  simpa only [Function.comp_def, visitedWalkPath] using
    (orientedWalkEdge_comp s (visitedWalkPath p) Subtype.val i).symm

/-- Even when the ambient tree has unvisited vertices, the actual support
restricted to visited vertices is a tree. -/
lemma visitedWalkSupport_isTree (T : Finset (V × V))
    (ht : (walkSupportGraph T).IsTree) (s : Fin n → Bool) (p : Fin (n+1) → V)
    (hsub : Finset.univ.image (orientedWalkEdge s p) ⊆ T) :
    (walkSupportGraph (Finset.univ.image (orientedWalkEdge s (visitedWalkPath p)))).IsTree := by
  classical
  let G := walkSupportGraph (Finset.univ.image (orientedWalkEdge s (visitedWalkPath p)))
  have hmem {a b : Set.range p}
      (h : (a,b) ∈ Finset.univ.image (orientedWalkEdge s (visitedWalkPath p))) :
      (a.val,b.val) ∈ T := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
    have hv := congrArg (Prod.map Subtype.val Subtype.val) hi
    rw [visitedWalkEdge_val] at hv
    exact hsub (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hv⟩)
  let f : G →g walkSupportGraph T :=
    { toFun := Subtype.val
      map_rel' := by
        intro a b hab
        exact ⟨fun h => hab.1 (Subtype.ext h),
          hab.2.imp (fun h => hmem h) (fun h => hmem h)⟩ }
  exact ⟨orientedWalk_support_connected s (visitedWalkPath p)
    (visitedWalkPath_surjective p), ht.isAcyclic.comap f Subtype.val_injective⟩

#print axioms visitedWalkPath
#print axioms visitedWalkPath_surjective
#print axioms orientedWalkEdge_comp
#print axioms visitedWalkEdge_val
#print axioms visitedWalkSupport_isTree
end SpectralRadiusUpperTail
