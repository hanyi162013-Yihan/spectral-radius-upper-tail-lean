import SpectralRadiusUpperTail.OrientedSegmentChain
import Mathlib.Data.List.OfFn

namespace SpectralRadiusUpperTail
variable {σ V : Type*}

/-- Recover an actual finite vertex path from a chain of primitive tokens. -/
lemma OrientedSegmentChain.exists_fin_path {ends : σ → V × V} {a b : V}
    {L : List (σ × Bool)} (h : OrientedSegmentChain ends a b L) :
    ∃ v : Fin (L.length+1) → V, v 0 = a ∧ v (Fin.last L.length) = b ∧
      ∀ i : Fin L.length,
        segmentTokenStart ends (L.get i) = v i.castSucc ∧
        segmentTokenFinish ends (L.get i) = v i.succ := by
  induction h with
  | nil a =>
    refine ⟨fun _ => a,rfl,rfl,?_⟩
    intro i
    exact Fin.elim0 i
  | @cons t b L h ih =>
    obtain ⟨v,hv0,hvlast,hv⟩ := ih
    let w : Fin ((t::L).length+1) → V := Fin.cases (segmentTokenStart ends t) v
    refine ⟨w,rfl,?_,?_⟩
    · change w (Fin.last (L.length+1)) = b
      rw [← Fin.succ_last]
      exact hvlast
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨rfl,hv0.symm⟩
      · change segmentTokenStart ends (L.get j) = v j.castSucc ∧
          segmentTokenFinish ends (L.get j) = v j.succ
        exact hv j

#print axioms OrientedSegmentChain.exists_fin_path
end SpectralRadiusUpperTail
