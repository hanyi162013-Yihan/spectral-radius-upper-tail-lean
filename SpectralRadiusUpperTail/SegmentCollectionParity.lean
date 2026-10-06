import SpectralRadiusUpperTail.SegmentRoute
import SpectralRadiusUpperTail.SegmentChainBoundaryParity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Nat

namespace SpectralRadiusUpperTail
variable {σ V : Type*} [DecidableEq V]

lemma segmentEndpointCount_append {α : Type*} (start finish : α → V)
    (L K : List α) (x : V) :
    segmentEndpointCount start finish (L++K) x =
      segmentEndpointCount start finish L x + segmentEndpointCount start finish K x := by
  simp [segmentEndpointCount,List.map_append,List.sum_append]

lemma segmentCollection_boundary_even (ends : σ → V × V) (K : List (SegmentRoute V σ))
    (hK : ∀ p ∈ K, OrientedSegmentChain ends p.start p.finish p.tokens) (x : V) :
    Even (segmentEndpointCount (segmentTokenStart ends) (segmentTokenFinish ends)
      (K.flatMap SegmentRoute.tokens) x +
        segmentEndpointCount SegmentRoute.start SegmentRoute.finish K x) := by
  induction K with
  | nil => simp [segmentEndpointCount]
  | cons p K ih =>
    have hp := (hK p (by simp)).boundary_even x
    have ht := ih (fun q hq => hK q (by simp [hq]))
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := ht
    refine ⟨a+b,?_⟩
    simp only [List.flatMap_cons,segmentEndpointCount_append,segmentEndpointCount_cons]
    omega

lemma segmentEndpointCount_even_of_counts [DecidableEq σ] [BEq σ] [LawfulBEq σ] (start finish : σ → V)
    (L : List σ) (heven : ∀ i, Even (L.count i)) (x : V) :
    Even (segmentEndpointCount start finish L x) := by
  unfold segmentEndpointCount
  rw [Finset.sum_list_map_count]
  apply Finset.even_sum
  intro i _
  simpa only [smul_eq_mul,List.count_eq_countP,Bool.beq_eq_decide_eq] using (heven i).mul_right
    ((if start i = x then 1 else 0) + (if finish i = x then 1 else 0))

/-- If the primitive labels occur evenly across valid path segments, the
endpoint multigraph of those segments has even degree at every vertex. -/
lemma segmentCollection_endpoint_even [DecidableEq σ] [BEq σ] [LawfulBEq σ] (ends : σ → V × V)
    (K : List (SegmentRoute V σ))
    (hK : ∀ p ∈ K, OrientedSegmentChain ends p.start p.finish p.tokens)
    (hc : ∀ i, Even (((K.flatMap SegmentRoute.tokens).map Prod.fst).count i)) :
    ∀ x, Even (segmentEndpointCount SegmentRoute.start SegmentRoute.finish K x) := by
  intro x
  have hb := segmentCollection_boundary_even ends K hK x
  have he := segmentEndpointCount_even_of_counts (fun i => (ends i).1)
    (fun i => (ends i).2) ((K.flatMap SegmentRoute.tokens).map Prod.fst) hc x
  rw [← segmentToken_endpoint_count ends (K.flatMap SegmentRoute.tokens) x] at he
  rw [even_iff_two_dvd,Nat.dvd_iff_mod_eq_zero] at hb he ⊢
  omega

#print axioms segmentEndpointCount_append
#print axioms segmentCollection_boundary_even
#print axioms segmentEndpointCount_even_of_counts
#print axioms segmentCollection_endpoint_even
end SpectralRadiusUpperTail
