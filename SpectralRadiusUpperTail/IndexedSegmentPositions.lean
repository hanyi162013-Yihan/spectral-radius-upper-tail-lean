import SpectralRadiusUpperTail.SurvivingPositionChunks
import Mathlib.Data.List.GetD

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

noncomputable def DefectRouteCertificate.segmentPositions (c : DefectRouteCertificate s v)
    (i : Fin c.segments.length) : List (Fin (2*r)) :=
  c.segmentPositionChunks.getD i.val []

lemma DefectRouteCertificate.segmentPositions_payloads (c : DefectRouteCertificate s v)
    (i : Fin c.segments.length) :
    (c.segmentPositions i).map c.originalToken = (c.segments.get i).tokens := by
  have h := congrArg (fun L : List (List ((V × V) × Bool)) => L.getD i.val [])
    c.segmentPositionChunks_payloads
  have hl := List.getD_map c.segmentPositionChunks ([] : List (Fin (2*r)))
    (n := i.val) (List.map c.originalToken)
  change (c.segmentPositionChunks.map (List.map c.originalToken)).getD i.val [] =
    (c.segmentPositions i).map c.originalToken at hl
  have hr : (c.segments.map SegmentRoute.tokens).getD i.val [] = (c.segments.get i).tokens := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt)]
    simp only [List.getElem_map]
    rfl
  exact hl.symm.trans (h.trans hr)

lemma DefectRouteCertificate.segmentPositions_length (c : DefectRouteCertificate s v)
    (i : Fin c.segments.length) :
    (c.segmentPositions i).length = (c.segments.get i).tokens.length := by
  simpa only [List.length_map] using congrArg List.length (c.segmentPositions_payloads i)

lemma DefectRouteCertificate.segmentPositions_nonempty (c : DefectRouteCertificate s v)
    (i : Fin c.segments.length) : c.segmentPositions i ≠ [] := by
  intro he
  have h := c.segmentPositions_payloads i
  rw [he,List.map_nil] at h
  exact (c.segments_valid _ (List.get_mem _ i)).2 h.symm

lemma DefectRouteCertificate.segmentPositions_ofFn (c : DefectRouteCertificate s v) :
    List.ofFn c.segmentPositions = c.segmentPositionChunks := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using c.segmentPositionChunks_length.symm
  · intro i hi hj
    simp only [List.getElem_ofFn,DefectRouteCertificate.segmentPositions]
    exact List.getD_eq_getElem _ _ hj

lemma DefectRouteCertificate.segmentPositions_flatten (c : DefectRouteCertificate s v) :
    (List.ofFn c.segmentPositions).flatten = c.survivingPositions := by
  rw [c.segmentPositions_ofFn,c.segmentPositionChunks_flatten]

#print axioms DefectRouteCertificate.segmentPositions
#print axioms DefectRouteCertificate.segmentPositions_payloads
#print axioms DefectRouteCertificate.segmentPositions_length
#print axioms DefectRouteCertificate.segmentPositions_nonempty
#print axioms DefectRouteCertificate.segmentPositions_ofFn
#print axioms DefectRouteCertificate.segmentPositions_flatten
end SpectralRadiusUpperTail
