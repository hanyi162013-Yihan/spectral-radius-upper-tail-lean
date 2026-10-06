import SpectralRadiusUpperTail.OrientedWalkDefectPruning
import SpectralRadiusUpperTail.FinitePathSegmentChain
import SpectralRadiusUpperTail.SegmentChainCut
import SpectralRadiusUpperTail.FiniteWordListCount

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

/-- Actual nonzero words admit at most 8g+1 valid nonempty surviving segments.
Their primitive token order is unchanged, and every surviving entry has exactly
two occurrences in a directed spanning tree. This is a decomposition theorem,
not yet a count of the original canonical patterns. -/
lemma orientedWalk_defect_segments (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0)
    (s : Fin (2*r) → Bool) (v : Fin (2*r+1) → ι) (hcover : Function.Surjective v)
    (hn : (∫ x : ι × ι → 𝕂, (∏ a, if s a then star (x (orientedWalkEdge s v a))
      else x (orientedWalkEdge s v a)) ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0) :
    ∃ (T : Finset (ι × ι)) (K : List (SegmentRoute ι (ι × ι))),
      T ⊆ Finset.univ.image (orientedWalkEdge s v) ∧
      (walkSupportGraph T).IsTree ∧ T.card + 1 = Fintype.card ι ∧
      (∀ a b, (a,b) ∈ T → a ≠ b) ∧
      (∀ a b, (a,b) ∈ T → (b,a) ∉ T) ∧
      (∀ p ∈ K, p.Valid (fun e => e)) ∧
      K.length ≤ 8*(r+1-Fintype.card ι)+1 ∧
      K.flatMap SegmentRoute.tokens =
        (List.ofFn (fun i => (orientedWalkEdge s v i,s i))).filter
          (fun t => decide (t.1 ∈ T ∧ entryMultiplicity (orientedWalkEdge s v) t.1 = 2)) ∧
      (∀ j, (((K.flatMap SegmentRoute.tokens).map Prod.fst).count j) =
        if j ∈ T ∧ entryMultiplicity (orientedWalkEdge s v) j = 2 then 2 else 0) := by
  let e := orientedWalkEdge s v
  obtain ⟨T,D,hT,htree,hcard,hloop,hop,hD,hsurvive⟩ :=
    orientedWalk_exists_defect_pruning μ hm s v hcover hn
  let keep : ι × ι → Bool := fun j => decide (j ∈ T ∧ entryMultiplicity e j = 2)
  obtain ⟨K,hK,hflat,hsize⟩ := (orientedWalk_segmentChain s v).cut
    (fun t => !(keep t.1))
  simp only [Bool.not_not] at hflat
  have hDset : Finset.univ.filter (fun i => !(keep (e i))) = D := by
    ext i
    have hh := (not_congr (hsurvive i)).symm
    simp [keep,e] at hh ⊢
    tauto
  have hdel : ((List.ofFn (fun i => (e i,s i))).filter (fun t => !(keep t.1))).length = D.card := by
    rw [list_ofFn_filter_length]
    exact congrArg Finset.card hDset
  have hmap : ((K.flatMap SegmentRoute.tokens).map Prod.fst) =
      (List.ofFn e).filter keep := by
    rw [hflat]
    have hh := List.filter_map (f := Prod.fst) (p := keep)
      (l := List.ofFn (fun i => (e i,s i)))
    simpa only [List.map_ofFn,Function.comp_def] using hh.symm
  refine ⟨T,K,hT,htree,hcard,hloop,hop,hK,?_,hflat,?_⟩
  · rw [hdel] at hsize
    omega
  · intro j
    rw [hmap,list_filter_count (List.ofFn e) keep j,list_ofFn_entryMultiplicity e j]
    change (if keep j then entryMultiplicity e j else 0) =
      if j ∈ T ∧ entryMultiplicity e j = 2 then 2 else 0
    by_cases hj : j ∈ T ∧ entryMultiplicity e j = 2
    · simp [keep,hj,hj.2]
    · simp [keep,hj]

#print axioms orientedWalk_defect_segments
end SpectralRadiusUpperTail
