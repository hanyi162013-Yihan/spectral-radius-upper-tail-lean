import SpectralRadiusUpperTail.OrientedWalkDefectClosedRoutes
import SpectralRadiusUpperTail.TreeRouteDoubleEntries
import SpectralRadiusUpperTail.SegmentRouteMatching
import SpectralRadiusUpperTail.ChosenTreePruningBudget

namespace SpectralRadiusUpperTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

/-- Expand an indexed whole-segment rearrangement into primitive routes. -/
def expandedDefectRoutes (K : List (SegmentRoute ι (ι × ι)))
    (C : List (SegmentRoute ι (Fin K.length))) : List (SegmentRoute ι (ι × ι)) :=
  C.map (expandSegmentRoute (fun i => (K.get i).tokens))

/-- A checked defect-decomposition certificate. It contains actual ordered
surviving segments and their once-only rearrangement, not an assumed injection
from canonical patterns into codes. That counting injection remains separate. -/
structure DefectRouteCertificate (s : Fin (2*r) → Bool) (v : Fin (2*r+1) → ι) where
  treeEntries : Finset (ι × ι)
  segments : List (SegmentRoute ι (ι × ι))
  tours : List (SegmentRoute ι (Fin segments.length))
  tree_subset : treeEntries ⊆ Finset.univ.image (orientedWalkEdge s v)
  tree : (walkSupportGraph treeEntries).IsTree
  tree_card : treeEntries.card+1 = Fintype.card ι
  no_loops : ∀ a b, (a,b) ∈ treeEntries → a ≠ b
  no_opposites : ∀ a b, (a,b) ∈ treeEntries → (b,a) ∉ treeEntries
  deletion_budget :
    (Finset.univ.filter (fun i => entryMultiplicity (orientedWalkEdge s v)
      (orientedWalkEdge s v i) ≠ 2 ∨ orientedWalkEdge s v i ∉ treeEntries)).card ≤
        8*(r+1-Fintype.card ι)
  segments_valid : ∀ p ∈ segments, p.Valid (fun e => e)
  segment_budget : segments.length ≤ 8*(r+1-Fintype.card ι)+1
  surviving_order : segments.flatMap SegmentRoute.tokens =
    (List.ofFn (fun i => (orientedWalkEdge s v i,s i))).filter
      (fun t => decide (t.1 ∈ treeEntries ∧ entryMultiplicity (orientedWalkEdge s v) t.1 = 2))
  segment_permutation : (tours.flatMap (fun p => p.tokens.map Prod.fst)).Perm
    (List.ofFn (fun i : Fin segments.length => i))
  tour_budget : tours.length ≤ segments.length
  closed_routes : ∀ p ∈ expandedDefectRoutes segments tours,
    p.Valid (fun e => e) ∧ p.start = p.finish
  total_entry_counts : ∀ j,
    ((expandedDefectRoutes segments tours).flatMap (fun p => p.tokens.map Prod.fst)).count j =
      if j ∈ treeEntries ∧ entryMultiplicity (orientedWalkEdge s v) j = 2 then 2 else 0
  route_entry_support : ∀ p ∈ expandedDefectRoutes segments tours,
    ∀ t ∈ p.tokens, t.1 ∈ treeEntries
  route_double_entries : ∀ p ∈ expandedDefectRoutes segments tours,
    ∀ t ∈ p.tokens, (p.tokens.map Prod.fst).count t.1 = 2
  route_matching : ∀ p ∈ expandedDefectRoutes segments tours,
    ∃ f : SignedNoncrossingMatching (fun i : Fin p.tokens.length => (p.tokens.get i).2),
      ∀ i, (p.tokens.get (f.val.val i)).1 = (p.tokens.get i).1

open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- Actual nonzero centered iid words supply the full pruning/reordering
certificate, including per-tour double entries and actual signed noncrossing
matchings. No defective-pattern cardinality bound is assumed or asserted. -/
lemma orientedWalk_defect_route_certificate (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0)
    (s : Fin (2*r) → Bool) (v : Fin (2*r+1) → ι) (hcover : Function.Surjective v)
    (hn : (∫ x : ι × ι → 𝕂, (∏ a, if s a then star (x (orientedWalkEdge s v a))
      else x (orientedWalkEdge s v a)) ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0) :
    Nonempty (DefectRouteCertificate s v) := by
  obtain ⟨T,K,C,hT,htree,hcard,hloop,hop,hK,hsize,hflat,hperm,hClen,hQ,hcounts⟩ :=
    orientedWalk_defect_closed_routes μ hm s v hcover hn
  let Q := expandedDefectRoutes K C
  have hQ' : ∀ p ∈ Q, p.Valid (fun e => e) ∧ p.start = p.finish := hQ
  have hcounts' : ∀ j, (Q.flatMap (fun p => p.tokens.map Prod.fst)).count j =
      if j ∈ T ∧ entryMultiplicity (orientedWalkEdge s v) j = 2 then 2 else 0 := hcounts
  have hsupp : ∀ p ∈ Q, ∀ t ∈ p.tokens, t.1 ∈ T := by
    apply route_entry_support_of_total_count T Q
    intro e he
    rw [hcounts' e]
    simp [he]
  have htwo : ∀ e, (Q.flatMap (fun p => p.tokens.map Prod.fst)).count e ≤ 2 := by
    intro e
    rw [hcounts' e]
    split_ifs <;> omega
  have hdouble : ∀ p ∈ Q, ∀ t ∈ p.tokens, (p.tokens.map Prod.fst).count t.1 = 2 := by
    intro p hp t ht
    have hh := closedTreeRoutes_entry_zero_or_two T htree hop Q hQ' hsupp htwo p hp t.1
    have hpos : 0 < (p.tokens.map Prod.fst).count t.1 :=
      List.count_pos_iff.mpr (List.mem_map.mpr ⟨t,ht,rfl⟩)
    omega
  have hmatching : ∀ p ∈ Q,
      ∃ f : SignedNoncrossingMatching (fun i : Fin p.tokens.length => (p.tokens.get i).2),
        ∀ i, (p.tokens.get (f.val.val i)).1 = (p.tokens.get i).1 := by
    intro p hp
    exact treeRoute_signed_matching T htree hloop hop p (hQ' p hp).1.1
      (hQ' p hp).2 (hsupp p hp) (hdouble p hp)
  exact ⟨{
    treeEntries := T
    segments := K
    tours := C
    tree_subset := hT
    tree := htree
    tree_card := hcard
    no_loops := hloop
    no_opposites := hop
    deletion_budget := orientedWalk_chosen_tree_pruning_budget μ hm s v hcover hn T hT hcard
    segments_valid := hK
    segment_budget := hsize
    surviving_order := hflat
    segment_permutation := hperm
    tour_budget := hClen
    closed_routes := hQ'
    total_entry_counts := hcounts
    route_entry_support := hsupp
    route_double_entries := hdouble
    route_matching := hmatching }⟩

#print axioms expandedDefectRoutes
#print axioms DefectRouteCertificate
#print axioms orientedWalk_defect_route_certificate
end SpectralRadiusUpperTail
