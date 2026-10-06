import SpectralRadiusUpperTail.IndexedSegmentPositions
import SpectralRadiusUpperTail.PositionArrangementDecoder

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

lemma DefectRouteCertificate.survivingPositions_eq_retainedList (c : DefectRouteCertificate s v) :
    c.survivingPositions = retainedPositionList c.deletedPositions := by
  classical
  unfold DefectRouteCertificate.survivingPositions retainedPositionList
  congr 1
  funext i
  simp [DefectRouteCertificate.deletedPositions,not_or,and_comm]

lemma DefectRouteCertificate.survivingPositions_length_le (c : DefectRouteCertificate s v) :
    c.survivingPositions.length ≤ 2*r := by
  classical
  exact (List.length_filter_le _ _).trans_eq List.length_ofFn

lemma DefectRouteCertificate.segmentPositions_length_le (c : DefectRouteCertificate s v)
    (i : Fin c.segments.length) : (c.segmentPositions i).length ≤ 2*r := by
  have hm : c.segmentPositions i ∈ List.ofFn c.segmentPositions := List.mem_ofFn.mpr ⟨i,rfl⟩
  have h := (List.sublist_flatten_of_mem hm).length_le
  rw [c.segmentPositions_flatten] at h
  exact h.trans c.survivingPositions_length_le

/-- Each segment length is itself a bounded ordinal, not an unbounded Nat
field hidden inside the combinatorial code. -/
noncomputable def DefectRouteCertificate.lengthCode (c : DefectRouteCertificate s v)
    (i : Fin c.segments.length) : Fin (2*r+1) :=
  ⟨(c.segmentPositions i).length,Nat.lt_succ_of_le (c.segmentPositions_length_le i)⟩

lemma DefectRouteCertificate.lengthCode_value (c : DefectRouteCertificate s v)
    (i : Fin c.segments.length) : (c.lengthCode i).val = (c.segments.get i).tokens.length :=
  c.segmentPositions_length i

lemma DefectRouteCertificate.lengthCode_list (c : DefectRouteCertificate s v) :
    List.ofFn (fun i => (c.lengthCode i).val) = c.segments.map (fun p => p.tokens.length) := by
  have h := congrArg (List.map (fun p : SegmentRoute V (V × V) => p.tokens.length))
    (List.ofFn_get c.segments)
  simpa only [List.map_ofFn,Function.comp_def,c.lengthCode_value] using h

lemma DefectRouteCertificate.decodePositionWord_eq (c : DefectRouteCertificate s v)
    (i : Fin c.segments.length) :
    decodePositionWord s c.deletedPositions c.lengthCode i =
      (c.segmentPositions i).map (fun j => (j,s j)) := by
  unfold decodePositionWord
  rw [c.lengthCode_list,← c.survivingPositions_eq_retainedList]
  rfl

#print axioms DefectRouteCertificate.survivingPositions_eq_retainedList
#print axioms DefectRouteCertificate.survivingPositions_length_le
#print axioms DefectRouteCertificate.segmentPositions_length_le
#print axioms DefectRouteCertificate.lengthCode
#print axioms DefectRouteCertificate.lengthCode_value
#print axioms DefectRouteCertificate.lengthCode_list
#print axioms DefectRouteCertificate.decodePositionWord_eq
end SpectralRadiusUpperTail
