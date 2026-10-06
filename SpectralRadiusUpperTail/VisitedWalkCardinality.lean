import SpectralRadiusUpperTail.VisitedWalkSupport
import SpectralRadiusUpperTail.OrientedSupportCardinality

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

lemma visitedWalkEdge_image (s : Fin n → Bool) (p : Fin (n+1) → V) :
    (Finset.univ.image (orientedWalkEdge s (visitedWalkPath p))).image
      (Prod.map Subtype.val Subtype.val) = Finset.univ.image (orientedWalkEdge s p) := by
  classical
  rw [Finset.image_image]
  congr 1
  funext i
  exact visitedWalkEdge_val s p i

/-- A tour visits exactly one more vertex than its number of distinct directed
edges, provided it lies in an oriented tree. No multiplicity or coverage of the
ambient vertex type is required. -/
lemma visitedWalk_card_eq_entries_add_one (T : Finset (V × V))
    (ht : (walkSupportGraph T).IsTree)
    (hloop : ∀ a b, (a,b) ∈ T → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (s : Fin n → Bool) (p : Fin (n+1) → V)
    (hsub : Finset.univ.image (orientedWalkEdge s p) ⊆ T) :
    Nat.card (Set.range p) = (Finset.univ.image (orientedWalkEdge s p)).card + 1 := by
  classical
  let E := Finset.univ.image (orientedWalkEdge s (visitedWalkPath p))
  have hv {a b : Set.range p} (h : (a,b) ∈ E) : (a.val,b.val) ∈ T := by
    apply hsub
    rw [← visitedWalkEdge_image s p]
    exact Finset.mem_image.mpr ⟨(a,b),h,rfl⟩
  have hc := oriented_tree_vertex_card E (visitedWalkSupport_isTree T ht s p hsub)
    (fun a b h hab => hloop a.val b.val (hv h) (congrArg Subtype.val hab))
    (fun a b h hba => hno a.val b.val (hv h) (hv hba))
  have hinj : Function.Injective (Prod.map (Subtype.val : Set.range p → V) (Subtype.val : Set.range p → V)) := by
    intro x y h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have he : E.card = (Finset.univ.image (orientedWalkEdge s p)).card := by
    rw [← visitedWalkEdge_image s p, Finset.card_image_of_injective _ hinj]
  rw [Nat.card_eq_fintype_card]
  exact hc.trans (congrArg (fun x => x+1) he)

#print axioms visitedWalkEdge_image
#print axioms visitedWalk_card_eq_entries_add_one
end SpectralRadiusUpperTail
