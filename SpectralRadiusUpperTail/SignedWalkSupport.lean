import SpectralRadiusUpperTail.WalkSupportCard
import SpectralRadiusUpperTail.IidSignedWalkIntegral

namespace SpectralRadiusUpperTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

def orientedWalkEdge (s : Fin k → Bool) (v : Fin (k+1) → ι) (a : Fin k) : ι × ι :=
  if s a then (v a.succ,v a.castSucc) else (v a.castSucc,v a.succ)

lemma orientedWalk_step_reachable (s : Fin k → Bool) (v : Fin (k+1) → ι) (a : Fin k) :
    (walkSupportGraph (Finset.univ.image (orientedWalkEdge s v))).Reachable
      (v a.castSucc) (v a.succ) := by
  have h : (walkSupportGraph (Finset.univ.image (orientedWalkEdge s v))).Reachable
      (orientedWalkEdge s v a).1 (orientedWalkEdge s v a).2 :=
    walkSupportGraph_edge_reachable _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩)
  cases hs : s a
  · have he : orientedWalkEdge s v a = (v a.castSucc,v a.succ) := by
      simp [orientedWalkEdge,hs]
    rw [he] at h
    exact h
  · have he : orientedWalkEdge s v a = (v a.succ,v a.castSucc) := by
      simp [orientedWalkEdge,hs]
    rw [he] at h
    exact h.symm

lemma orientedWalk_support_connected (s : Fin k → Bool) (v : Fin (k+1) → ι)
    (hcover : Function.Surjective v) :
    (walkSupportGraph (Finset.univ.image (orientedWalkEdge s v))).Connected := by
  have hr : ∀ a : Fin (k+1),
      (walkSupportGraph (Finset.univ.image (orientedWalkEdge s v))).Reachable (v 0) (v a) := by
    intro a
    induction a using Fin.induction with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ a ih => exact ih.trans (orientedWalk_step_reachable s v a)
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨v 0,fun x => ?_⟩
  obtain ⟨a,rfl⟩ := hcover x
  exact hr a

lemma orientedWalk_vertex_card_le (s : Fin k → Bool) (v : Fin (k+1) → ι)
    (hcover : Function.Surjective v) :
    Fintype.card ι ≤ (Finset.univ.image (orientedWalkEdge s v)).card+1 :=
  walkSupportGraph_vertex_card_le _ (orientedWalk_support_connected s v hcover)

#print axioms orientedWalkEdge
#print axioms orientedWalk_step_reachable
#print axioms orientedWalk_support_connected
#print axioms orientedWalk_vertex_card_le
end SpectralRadiusUpperTail
