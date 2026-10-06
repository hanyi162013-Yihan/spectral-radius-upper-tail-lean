import SpectralRadiusUpperTail.SignedWalkSupport
import SpectralRadiusUpperTail.WalkSupportOrientation

namespace SpectralRadiusUpperTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orientedEdgeSet_sym2_injective (E : Finset (ι × ι))
    (hno : ∀ a b, (a,b) ∈ E → (b,a) ∉ E) :
    Set.InjOn (fun e : ι × ι => s(e.1,e.2)) E := by
  intro e he f hf hsym
  rcases Sym2.eq_iff.mp hsym with h | h
  · exact Prod.ext h.1 h.2
  · have heq : e = (f.2,f.1) := Prod.ext h.1 h.2
    rw [heq] at he
    exact False.elim (hno f.1 f.2 hf he)

lemma orientedWalkEdge_sym2 {n : ℕ} (s : Fin n → Bool) (p : Fin (n+1) → ι) (i : Fin n) :
    s((orientedWalkEdge s p i).1,(orientedWalkEdge s p i).2) = s(p i.castSucc,p i.succ) := by
  cases hs : s i
  · simp only [orientedWalkEdge,hs,Bool.false_eq_true,if_false]
  · simp only [orientedWalkEdge,hs,if_true]
    exact Sym2.eq_swap

lemma orientedWalkEdge_eq_iff_geometric {n : ℕ} (s : Fin n → Bool) (p : Fin (n+1) → ι)
    (hno : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) →
      (b,a) ∉ Finset.univ.image (orientedWalkEdge s p)) (i j : Fin n) :
    orientedWalkEdge s p i = orientedWalkEdge s p j ↔
      s(p i.castSucc,p i.succ) = s(p j.castSucc,p j.succ) := by
  have hi : orientedWalkEdge s p i ∈ Finset.univ.image (orientedWalkEdge s p) :=
    Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have hj : orientedWalkEdge s p j ∈ Finset.univ.image (orientedWalkEdge s p) :=
    Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩
  rw [← orientedWalkEdge_sym2 s p i, ← orientedWalkEdge_sym2 s p j]
  exact ⟨fun h => congrArg (fun e : ι × ι => s(e.1,e.2)) h,
    fun h => orientedEdgeSet_sym2_injective _ hno hi hj h⟩

lemma orientedWalk_step_adj {n : ℕ} (s : Fin n → Bool) (p : Fin (n+1) → ι)
    (hloop : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) → a ≠ b)
    (i : Fin n) : (walkSupportGraph (Finset.univ.image (orientedWalkEdge s p))).Adj
      (p i.castSucc) (p i.succ) := by
  have hm : orientedWalkEdge s p i ∈ Finset.univ.image (orientedWalkEdge s p) :=
    Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have ha : (walkSupportGraph (Finset.univ.image (orientedWalkEdge s p))).Adj
      (orientedWalkEdge s p i).1 (orientedWalkEdge s p i).2 :=
    ⟨hloop _ _ hm,Or.inl hm⟩
  cases hs : s i
  · simpa only [orientedWalkEdge,hs,Bool.false_eq_true,if_false] using ha
  · have hh := ha.symm
    simpa only [orientedWalkEdge,hs,if_true] using hh

#print axioms orientedEdgeSet_sym2_injective
#print axioms orientedWalkEdge_sym2
#print axioms orientedWalkEdge_eq_iff_geometric
#print axioms orientedWalk_step_adj
end SpectralRadiusUpperTail
