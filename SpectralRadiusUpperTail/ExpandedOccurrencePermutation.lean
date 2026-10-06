import SpectralRadiusUpperTail.SegmentPayloadTransport
import Mathlib.Data.List.OfFn

namespace SpectralRadiusUpperTail
variable {A I V : Type*} [Fintype I] [DecidableEq V]

/-- A once-only segment permutation preserves the multiset of primitive
occurrence labels. Using original positions as labels gives a genuine
occurrence permutation, even when matrix entry labels repeat. -/
lemma expandedOccurrence_permutation
    (words : I → List (A × Bool)) (C : List (SegmentRoute V I)) (order : List I)
    (hperm : (C.flatMap (fun p => p.tokens.map Prod.fst)).Perm order) :
    ((C.map (expandSegmentRoute words)).flatMap (fun p => p.tokens.map Prod.fst)).Perm
      (order.flatMap (fun i => (words i).map Prod.fst)) := by
  classical
  apply Multiset.coe_eq_coe.mp
  rw [← segmentRoute_labels_sum,expandedSegmentCollection_labels]
  have hp := (hperm.map (fun i => ((words i).map Prod.fst : Multiset A))).sum_eq
  rw [hp]
  have hsum (K : List I) :
      (K.map (fun i => ((words i).map Prod.fst : Multiset A))).sum =
        ((K.flatMap (fun i => (words i).map Prod.fst) : List A) : Multiset A) := by
    induction K with
    | nil => simp
    | cons i K ih =>
      simp only [List.map_cons,List.sum_cons,List.flatMap_cons,ih]
      exact Multiset.coe_add _ _
  exact hsum order

/-- A family indexed by all finite segment positions therefore expands to
the same primitive occurrence list up to permutation. -/
lemma expandedOccurrence_ofFn_permutation {n : ℕ}
    (words : Fin n → List (A × Bool)) (C : List (SegmentRoute V (Fin n)))
    (hperm : (C.flatMap (fun p => p.tokens.map Prod.fst)).Perm
      (List.ofFn (fun i : Fin n => i))) :
    ((C.map (expandSegmentRoute words)).flatMap (fun p => p.tokens.map Prod.fst)).Perm
      (List.ofFn (fun i => (words i).map Prod.fst)).flatten := by
  have h := expandedOccurrence_permutation words C _ hperm
  simpa only [List.flatMap_def,List.map_ofFn,Function.comp_def] using h

#print axioms expandedOccurrence_permutation
#print axioms expandedOccurrence_ofFn_permutation
end SpectralRadiusUpperTail
