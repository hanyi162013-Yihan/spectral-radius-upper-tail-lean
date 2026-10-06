import SpectralRadiusUpperTail.SegmentRoute

namespace SpectralRadiusUpperTail
variable {σ V : Type*}

/-- Cutting a chain at deleted tokens yields exactly one more (possibly empty)
fragment than deleted tokens. The token order is preserved exactly. -/
lemma OrientedSegmentChain.cut_with_empty {ends : σ → V × V} {a b : V}
    {L : List (σ × Bool)} (h : OrientedSegmentChain ends a b L)
    (drop : σ × Bool → Bool) :
    ∃ (p : SegmentRoute V σ) (rest : List (SegmentRoute V σ)),
      p.start = a ∧
      (∀ q ∈ p::rest, OrientedSegmentChain ends q.start q.finish q.tokens) ∧
      (p::rest).flatMap SegmentRoute.tokens = L.filter (fun t => !(drop t)) ∧
      (p::rest).length = (L.filter drop).length + 1 := by
  induction h with
  | nil a =>
    refine ⟨⟨a,a,[]⟩,[],rfl,?_,by simp,by simp⟩
    intro q hq
    have hq : q = ⟨a,a,[]⟩ := by simpa using hq
    subst q
    exact .nil a
  | @cons t b L h ih =>
    obtain ⟨p,rest,hps,hchain,hflat,hcount⟩ := ih
    have hp := hchain p (by simp)
    cases hd : drop t with
    | false =>
      let q : SegmentRoute V σ :=
        ⟨segmentTokenStart ends t,p.finish,t::p.tokens⟩
      have hq : OrientedSegmentChain ends q.start q.finish q.tokens := by
        exact .cons t (hps ▸ hp)
      refine ⟨q,rest,rfl,?_,?_,?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hq
        · exact hchain u (List.mem_cons_of_mem p hu)
      · simpa [q,List.flatMap_cons,hd] using congrArg (List.cons t) hflat
      · simpa [hd] using hcount
    | true =>
      let q : SegmentRoute V σ := ⟨segmentTokenStart ends t,segmentTokenStart ends t,[]⟩
      refine ⟨q,p::rest,rfl,?_,?_,?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact .nil _
        · exact hchain u hu
      · simpa [q,List.flatMap_cons,hd] using hflat
      · simp only [List.length_cons,List.filter_cons,hd,ite_true] at hcount ⊢
        omega

/-- Removing empty fragments gives at most D+1 nonempty valid segments after
D deletions. Their flattened tokens are exactly the surviving original tokens. -/
lemma OrientedSegmentChain.cut {ends : σ → V × V} {a b : V}
    {L : List (σ × Bool)} (h : OrientedSegmentChain ends a b L)
    (drop : σ × Bool → Bool) :
    ∃ K : List (SegmentRoute V σ), (∀ p ∈ K, p.Valid ends) ∧
      K.flatMap SegmentRoute.tokens = L.filter (fun t => !(drop t)) ∧
      K.length ≤ (L.filter drop).length + 1 := by
  classical
  obtain ⟨p,rest,hps,hchain,hflat,hcount⟩ := h.cut_with_empty drop
  let K := (p::rest).filter (fun q => decide (q.tokens ≠ []))
  refine ⟨K,?_,?_,?_⟩
  · intro q hq
    have hq' : q ∈ p::rest ∧ q.tokens ≠ [] := by simpa [K] using hq
    exact ⟨hchain q hq'.1,hq'.2⟩
  · have he : ∀ J : List (SegmentRoute V σ),
        (J.filter (fun q => decide (q.tokens ≠ []))).flatMap SegmentRoute.tokens =
          J.flatMap SegmentRoute.tokens := by
      intro J
      induction J with
      | nil => simp
      | cons q J ih =>
        simp only [decide_not] at ih ⊢
        by_cases hq : q.tokens = [] <;> simp [hq,ih]
    exact (he (p::rest)).trans hflat
  · rw [← hcount]
    exact List.length_filter_le _ _

#print axioms OrientedSegmentChain.cut_with_empty
#print axioms OrientedSegmentChain.cut
end SpectralRadiusUpperTail
