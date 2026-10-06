import SpectralRadiusUpperTail.OrientedSegmentChain
import SpectralRadiusUpperTail.SignedWalkSupport
import Mathlib.Data.List.OfFn

namespace SpectralRadiusUpperTail
variable {σ V : Type*}

lemma orientedSegmentChain_of_fin_path (ends : σ → V × V) {n : ℕ}
    (t : Fin n → σ × Bool) (v : Fin (n+1) → V)
    (hs : ∀ i, segmentTokenStart ends (t i) = v i.castSucc)
    (hf : ∀ i, segmentTokenFinish ends (t i) = v i.succ) :
    OrientedSegmentChain ends (v 0) (v (Fin.last n)) (List.ofFn t) := by
  induction n with
  | zero => simpa using OrientedSegmentChain.nil (ends := ends) (v 0)
  | succ n ih =>
    rw [List.ofFn_succ]
    have hr := ih (fun i => t i.succ) (fun i => v i.succ)
      (fun i => hs i.succ) (fun i => hf i.succ)
    have hh : OrientedSegmentChain ends (segmentTokenFinish ends (t 0))
        (v (Fin.last (n+1))) (List.ofFn (fun i => t i.succ)) := by
      simpa only [hf 0,Fin.succ_last] using hr
    simpa only [hs 0,Fin.castSucc_zero] using OrientedSegmentChain.cons (t 0) hh

lemma orientedWalk_segmentChain {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (s : Fin n → Bool) (v : Fin (n+1) → ι) :
    OrientedSegmentChain (fun e : ι × ι => e) (v 0) (v (Fin.last n))
      (List.ofFn (fun i => (orientedWalkEdge s v i,s i))) := by
  apply orientedSegmentChain_of_fin_path
  · intro i
    cases hi : s i <;> simp [segmentTokenStart,orientedWalkEdge,hi]
  · intro i
    cases hi : s i <;> simp [segmentTokenFinish,orientedWalkEdge,hi]

#print axioms orientedSegmentChain_of_fin_path
#print axioms orientedWalk_segmentChain
end SpectralRadiusUpperTail
