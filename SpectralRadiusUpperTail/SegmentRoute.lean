import SpectralRadiusUpperTail.OrientedSegmentChain
import Mathlib.Data.Multiset.AddSub

namespace SpectralRadiusUpperTail
variable {σ V : Type*}

structure SegmentRoute (V σ : Type*) where
  start : V
  finish : V
  tokens : List (σ × Bool)

def SegmentRoute.Valid (ends : σ → V × V) (p : SegmentRoute V σ) : Prop :=
  OrientedSegmentChain ends p.start p.finish p.tokens ∧ p.tokens ≠ []

def SegmentRoute.reverse (p : SegmentRoute V σ) : SegmentRoute V σ :=
  ⟨p.finish,p.start,p.tokens.reverse.map segmentTokenReverse⟩

def SegmentRoute.join (p q : SegmentRoute V σ) : SegmentRoute V σ :=
  ⟨p.start,q.finish,p.tokens++q.tokens⟩

def SegmentRoute.labels (p : SegmentRoute V σ) : Multiset σ :=
  (p.tokens.map Prod.fst : List σ)

lemma SegmentRoute.reverse_valid (ends : σ → V × V) (p : SegmentRoute V σ)
    (h : p.Valid ends) : p.reverse.Valid ends := by
  refine ⟨h.1.reverse,?_⟩
  simpa [SegmentRoute.reverse] using h.2

lemma SegmentRoute.join_valid (ends : σ → V × V) (p q : SegmentRoute V σ)
    (hp : p.Valid ends) (hq : q.Valid ends) (h : p.finish = q.start) :
    (p.join q).Valid ends := by
  constructor
  · exact hp.1.append (h.symm ▸ hq.1)
  · intro hz
    exact hp.2 (List.append_eq_nil_iff.mp hz).1

lemma SegmentRoute.reverse_labels (p : SegmentRoute V σ) : p.reverse.labels = p.labels := by
  simp [SegmentRoute.reverse,SegmentRoute.labels,List.map_map,segmentTokenReverse,
    List.map_reverse,Function.comp_def]

lemma SegmentRoute.join_labels (p q : SegmentRoute V σ) :
    (p.join q).labels = p.labels + q.labels := by
  simp [SegmentRoute.join,SegmentRoute.labels,List.map_append,Multiset.coe_add]

def SegmentRoute.single (ends : σ → V × V) (i : σ) : SegmentRoute V σ :=
  ⟨(ends i).1,(ends i).2,[(i,false)]⟩

lemma SegmentRoute.single_valid (ends : σ → V × V) (i : σ) :
    (SegmentRoute.single ends i).Valid ends := by
  constructor
  · exact OrientedSegmentChain.singleton ends (i,false)
  · simp [SegmentRoute.single]

#print axioms SegmentRoute
#print axioms SegmentRoute.Valid
#print axioms SegmentRoute.reverse
#print axioms SegmentRoute.join
#print axioms SegmentRoute.labels
#print axioms SegmentRoute.reverse_valid
#print axioms SegmentRoute.join_valid
#print axioms SegmentRoute.reverse_labels
#print axioms SegmentRoute.join_labels
#print axioms SegmentRoute.single
#print axioms SegmentRoute.single_valid
end SpectralRadiusUpperTail
