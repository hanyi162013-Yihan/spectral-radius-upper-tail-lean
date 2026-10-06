import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
variable {σ V : Type*}

def segmentTokenStart (ends : σ → V × V) (t : σ × Bool) : V :=
  if t.2 then (ends t.1).2 else (ends t.1).1

def segmentTokenFinish (ends : σ → V × V) (t : σ × Bool) : V :=
  if t.2 then (ends t.1).1 else (ends t.1).2

def segmentTokenReverse (t : σ × Bool) : σ × Bool := (t.1,!t.2)

lemma segmentTokenReverse_start (ends : σ → V × V) (t : σ × Bool) :
    segmentTokenStart ends (segmentTokenReverse t) = segmentTokenFinish ends t := by
  cases ht : t.2 <;> simp [segmentTokenStart,segmentTokenFinish,segmentTokenReverse,ht]

lemma segmentTokenReverse_finish (ends : σ → V × V) (t : σ × Bool) :
    segmentTokenFinish ends (segmentTokenReverse t) = segmentTokenStart ends t := by
  cases ht : t.2 <;> simp [segmentTokenStart,segmentTokenFinish,segmentTokenReverse,ht]

/-- A chain of named segments; the Boolean records reversal of the WHOLE segment. -/
inductive OrientedSegmentChain (ends : σ → V × V) : V → V → List (σ × Bool) → Prop
  | nil (a : V) : OrientedSegmentChain ends a a []
  | cons (t : σ × Bool) {b : V} {L : List (σ × Bool)}
      (h : OrientedSegmentChain ends (segmentTokenFinish ends t) b L) :
      OrientedSegmentChain ends (segmentTokenStart ends t) b (t::L)

lemma OrientedSegmentChain.append {ends : σ → V × V} {a b c : V}
    {L K : List (σ × Bool)} (h : OrientedSegmentChain ends a b L)
    (hk : OrientedSegmentChain ends b c K) : OrientedSegmentChain ends a c (L++K) := by
  induction h with
  | nil a => exact hk
  | cons t h ih => exact .cons t (ih hk)

lemma OrientedSegmentChain.singleton (ends : σ → V × V) (t : σ × Bool) :
    OrientedSegmentChain ends (segmentTokenStart ends t) (segmentTokenFinish ends t) [t] :=
  .cons t (.nil _)

lemma OrientedSegmentChain.reverse {ends : σ → V × V} {a b : V}
    {L : List (σ × Bool)} (h : OrientedSegmentChain ends a b L) :
    OrientedSegmentChain ends b a (L.reverse.map segmentTokenReverse) := by
  induction h with
  | nil a => exact .nil a
  | cons t h ih =>
    rw [List.reverse_cons,List.map_append]
    apply ih.append
    simpa only [List.map_cons,List.map_nil,segmentTokenReverse_start,
      segmentTokenReverse_finish] using OrientedSegmentChain.singleton ends (segmentTokenReverse t)

#print axioms segmentTokenStart
#print axioms segmentTokenFinish
#print axioms segmentTokenReverse
#print axioms segmentTokenReverse_start
#print axioms segmentTokenReverse_finish
#print axioms OrientedSegmentChain
#print axioms OrientedSegmentChain.append
#print axioms OrientedSegmentChain.singleton
#print axioms OrientedSegmentChain.reverse
end SpectralRadiusUpperTail
