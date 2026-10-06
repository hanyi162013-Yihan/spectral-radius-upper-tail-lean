import SpectralRadiusUpperTail.OrientedWalkDefectSegments
import SpectralRadiusUpperTail.ReorderedSegmentRoutes

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

/-- Actual nonzero covered words can be pruned into at most 8g+1 segments and
reordered as closed routes. The certificate is a permutation of the original
segment indices and explicitly preserves all retained primitive entry counts. -/
lemma orientedWalk_defect_closed_routes (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0)
    (s : Fin (2*r) → Bool) (v : Fin (2*r+1) → ι) (hcover : Function.Surjective v)
    (hn : (∫ x : ι × ι → 𝕂, (∏ a, if s a then star (x (orientedWalkEdge s v a))
      else x (orientedWalkEdge s v a)) ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0) :
    ∃ (T : Finset (ι × ι)) (K : List (SegmentRoute ι (ι × ι)))
        (C : List (SegmentRoute ι (Fin K.length))),
      T ⊆ Finset.univ.image (orientedWalkEdge s v) ∧
      (walkSupportGraph T).IsTree ∧ T.card + 1 = Fintype.card ι ∧
      (∀ a b, (a,b) ∈ T → a ≠ b) ∧
      (∀ a b, (a,b) ∈ T → (b,a) ∉ T) ∧
      (∀ p ∈ K, p.Valid (fun e => e)) ∧
      K.length ≤ 8*(r+1-Fintype.card ι)+1 ∧
      K.flatMap SegmentRoute.tokens =
        (List.ofFn (fun i => (orientedWalkEdge s v i,s i))).filter
          (fun t => decide (t.1 ∈ T ∧ entryMultiplicity (orientedWalkEdge s v) t.1 = 2)) ∧
      (C.flatMap (fun p => p.tokens.map Prod.fst)).Perm (List.ofFn (fun i : Fin K.length => i)) ∧
      C.length ≤ K.length ∧
      (∀ p ∈ C.map (expandSegmentRoute (fun i => (K.get i).tokens)),
        p.Valid (fun e => e) ∧ p.start = p.finish) ∧
      (∀ j, (((C.map (expandSegmentRoute (fun i => (K.get i).tokens))).flatMap
        (fun p => p.tokens.map Prod.fst)).count j) =
          if j ∈ T ∧ entryMultiplicity (orientedWalkEdge s v) j = 2 then 2 else 0) := by
  obtain ⟨T,K,hT,htree,hcard,hloop,hop,hK,hsize,hflat,hcounts⟩ :=
    orientedWalk_defect_segments μ hm s v hcover hn
  have he : ∀ j, Even (((K.flatMap SegmentRoute.tokens).map Prod.fst).count j) := by
    intro j
    rw [hcounts]
    split_ifs <;> decide
  obtain ⟨C,hperm,hC,hClen,hQ,hQperm⟩ := reorderSegments_into_closed_routes (fun e => e) K hK he
  refine ⟨T,K,C,hT,htree,hcard,hloop,hop,hK,hsize,hflat,hperm,hClen,hQ,?_⟩
  intro j
  rw [hQperm.count_eq j]
  simpa only [List.map_flatMap,Function.comp_def] using hcounts j

#print axioms orientedWalk_defect_closed_routes
end SpectralRadiusUpperTail
