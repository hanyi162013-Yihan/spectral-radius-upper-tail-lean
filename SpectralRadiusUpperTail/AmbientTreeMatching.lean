import SpectralRadiusUpperTail.OrientedTreePartnerNoncrossing
import SpectralRadiusUpperTail.OrientedTreePartnerSigns
import SpectralRadiusUpperTail.SignedBlockMatchingCount

namespace SpectralRadiusUpperTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

lemma walkSupportGraph_mono {E F : Finset (ι × ι)} (h : E ⊆ F) :
    walkSupportGraph E ≤ walkSupportGraph F := by
  intro a b hab
  exact ⟨hab.1,hab.2.imp (fun he => h he) (fun he => h he)⟩

/-- A closed double-edge path inside an ambient oriented tree supplies a signed
noncrossing matching. Vertices of the ambient tree need not all be visited. -/
lemma ambientTree_signed_matching (T : Finset (ι × ι)) (ht : (walkSupportGraph T).IsTree)
    (hloop : ∀ a b, (a,b) ∈ T → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (s : Fin n → Bool) (p : Fin (n+1) → ι)
    (hsub : Finset.univ.image (orientedWalkEdge s p) ⊆ T)
    (hm : ∀ i, entryMultiplicity (orientedWalkEdge s p) (orientedWalkEdge s p i) = 2)
    (hclosed : p (Fin.last n) = p 0) :
    ∃ f : SignedNoncrossingMatching s, ∀ i,
      orientedWalkEdge s p (f.val.val i) = orientedWalkEdge s p i := by
  let G := walkSupportGraph T
  let f := doubleWordPartner (orientedWalkEdge s p) hm
  have hloop' : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) → a ≠ b :=
    fun a b hab => hloop a b (hsub hab)
  have hno' : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) →
      (b,a) ∉ Finset.univ.image (orientedWalkEdge s p) :=
    fun a b hab hba => hno a b (hsub hab) (hsub hba)
  have hadj (i : Fin n) : G.Adj (p i.castSucc) (p i.succ) :=
    walkSupportGraph_mono hsub (orientedWalk_step_adj s p hloop' i)
  have hnc : ∀ i k, i < k → k < f i → f i < f k → False := by
    intro i k hik hkj hjl
    have hb : G.IsBridge s(p i.castSucc,p i.succ) :=
      SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ht.isAcyclic (hadj i)
    apply finiteBridgePath_no_interleaving G (p i.castSucc) (p i.succ) hb p i k (f i) (f k)
      hik hkj hjl hadj
    · exact (orientedWalkEdge_eq_iff_geometric s p hno' (f i) i).mp
        (doubleWordPartner_spec (orientedWalkEdge s p) hm i).2
    · intro j hij hjl hji he
      have he' := (orientedWalkEdge_eq_iff_geometric s p hno' j i).mpr he
      rcases (doubleWord_entry_eq_iff (orientedWalkEdge s p) hm i j).mp he' with h | h
      · exact (ne_of_gt hij) h
      · exact hji h
    · exact (orientedWalkEdge_eq_iff_geometric s p hno' k (f k)).mp
        (doubleWordPartner_spec (orientedWalkEdge s p) hm k).2.symm
  have hs : ∀ i, s (f i) ≠ s i := by
    intro i
    obtain ⟨j,hj⟩ := closedTreePath_reverse_occurrence G ht p hadj hclosed i
    have hg : s(p j.castSucc,p j.succ) = s(p i.castSucc,p i.succ) := by
      rw [hj.1,hj.2]
      exact Sym2.eq_swap
    have he := (orientedWalkEdge_eq_iff_geometric s p hno' j i).mpr hg
    have hji : j ≠ i := by
      intro h
      subst j
      exact (hadj i).ne hj.1
    have hpartner : j = f i :=
      ((doubleWord_entry_eq_iff (orientedWalkEdge s p) hm i j).mp he).resolve_left hji
    rw [← hpartner]
    exact orientedWalk_sign_ne_of_reverse s p i j he hj (hadj i).ne
  refine ⟨⟨⟨f,doubleWordPartner_involutive _ hm,
    (fun i => (doubleWordPartner_spec _ hm i).1),hnc⟩,hs⟩,?_⟩
  intro i
  exact (doubleWordPartner_spec _ hm i).2

#print axioms walkSupportGraph_mono
#print axioms ambientTree_signed_matching
end SpectralRadiusUpperTail
