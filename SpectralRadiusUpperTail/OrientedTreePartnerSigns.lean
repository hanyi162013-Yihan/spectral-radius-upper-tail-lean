import SpectralRadiusUpperTail.OrientedEdgeSymmetry
import SpectralRadiusUpperTail.DoubleWordPartnerFiber
import SpectralRadiusUpperTail.TreePathReverseOccurrence

namespace SpectralRadiusUpperTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

lemma orientedWalk_sign_ne_of_reverse (s : Fin n → Bool) (p : Fin (n+1) → ι)
    (i j : Fin n) (he : orientedWalkEdge s p j = orientedWalkEdge s p i)
    (hrev : p j.castSucc = p i.succ ∧ p j.succ = p i.castSucc)
    (hne : p i.castSucc ≠ p i.succ) : s j ≠ s i := by
  intro hs
  cases hi : s i
  · have hc := congrArg Prod.fst he
    simp only [orientedWalkEdge,hs,hi,Bool.false_eq_true,if_false,Prod.fst] at hc
    rw [hrev.1] at hc
    exact hne hc.symm
  · have hc := congrArg Prod.fst he
    simp only [orientedWalkEdge,hs,hi,if_true,Prod.fst] at hc
    rw [hrev.2] at hc
    exact hne hc

/-- Paired entries on a closed oriented tree path have opposite transpose signs,
including for real-valued entry laws. -/
lemma orientedTree_partner_opposite_signs (s : Fin n → Bool) (p : Fin (n+1) → ι)
    (ht : (walkSupportGraph (Finset.univ.image (orientedWalkEdge s p))).IsTree)
    (hloop : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) →
      (b,a) ∉ Finset.univ.image (orientedWalkEdge s p))
    (hm : ∀ i, entryMultiplicity (orientedWalkEdge s p) (orientedWalkEdge s p i) = 2)
    (hclosed : p (Fin.last n) = p 0) (i : Fin n) :
    s (doubleWordPartner (orientedWalkEdge s p) hm i) ≠ s i := by
  let G := walkSupportGraph (Finset.univ.image (orientedWalkEdge s p))
  have hadj (t : Fin n) : G.Adj (p t.castSucc) (p t.succ) := orientedWalk_step_adj s p hloop t
  obtain ⟨j,hj⟩ := closedTreePath_reverse_occurrence G ht p hadj hclosed i
  have hgeom : s(p j.castSucc,p j.succ) = s(p i.castSucc,p i.succ) := by
    rw [hj.1,hj.2]
    exact Sym2.eq_swap
  have he := (orientedWalkEdge_eq_iff_geometric s p hno j i).mpr hgeom
  have hji : j ≠ i := by
    intro h
    subst j
    exact (hadj i).ne hj.1
  have hp : j = doubleWordPartner (orientedWalkEdge s p) hm i :=
    ((doubleWord_entry_eq_iff (orientedWalkEdge s p) hm i j).mp he).resolve_left hji
  rw [← hp]
  exact orientedWalk_sign_ne_of_reverse s p i j he hj (hadj i).ne

#print axioms orientedWalk_sign_ne_of_reverse
#print axioms orientedTree_partner_opposite_signs
end SpectralRadiusUpperTail
