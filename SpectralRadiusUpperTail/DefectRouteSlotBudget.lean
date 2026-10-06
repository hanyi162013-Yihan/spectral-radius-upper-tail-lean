import SpectralRadiusUpperTail.DefectRouteGluing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

lemma finite_list_length_le_of_counts {A : Type*} [Fintype A] [DecidableEq A] [BEq A] [LawfulBEq A]
    (L K : List A) (h : ∀ a, L.count a ≤ K.count a) : L.length ≤ K.length := by
  classical
  have hs (J : List A) : (∑ a : A, J.count a) = J.length := by
    simpa [list_count_indicator_sum] using (Multiset.sum_count_eq_card (s := Finset.univ) (m := (J : Multiset A))
      (fun _ _ => Finset.mem_univ _))
  rw [← hs L, ← hs K]
  exact Finset.sum_le_sum (fun a _ => h a)

lemma DefectRouteCertificate.total_primitive_length_le (c : DefectRouteCertificate s v) :
    ((expandedDefectRoutes c.segments c.tours).flatMap (fun p => p.tokens.map Prod.fst)).length
      ≤ 2*r := by
  classical
  have h := finite_list_length_le_of_counts
    ((expandedDefectRoutes c.segments c.tours).flatMap (fun p => p.tokens.map Prod.fst))
    (List.ofFn (orientedWalkEdge s v)) (fun e => ?_)
  · simpa only [List.length_ofFn] using h
  · rw [c.total_entry_counts e, list_ofFn_entryMultiplicity]
    split_ifs with he
    · exact le_of_eq he.2.symm
    · exact Nat.zero_le _

lemma DefectRouteCertificate.sum_tour_lengths (c : DefectRouteCertificate s v) :
    (∑ i : Fin (expandedDefectRoutes c.segments c.tours).length,
      ((expandedDefectRoutes c.segments c.tours).get i).tokens.length) =
    ((expandedDefectRoutes c.segments c.tours).flatMap (fun p => p.tokens.map Prod.fst)).length := by
  let Q := expandedDefectRoutes c.segments c.tours
  have h := congrArg (fun L : List (SegmentRoute V (V × V)) =>
    (L.map (fun p => p.tokens.length)).sum) (List.ofFn_get Q)
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_def,List.length_flatMap,
    List.length_map] using h

lemma DefectRouteCertificate.tour_count_le_primitive_length (c : DefectRouteCertificate s v) :
    (expandedDefectRoutes c.segments c.tours).length ≤
      ((expandedDefectRoutes c.segments c.tours).flatMap (fun p => p.tokens.map Prod.fst)).length := by
  rw [← c.sum_tour_lengths]
  calc
    _ = ∑ _i : Fin (expandedDefectRoutes c.segments c.tours).length, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ =>
      Nat.succ_le_of_lt (List.length_pos_iff.mpr (c.closed_routes _ (List.get_mem _ i)).1.2))

/-- There are at most twice the original primitive word length many local
vertex slots. These bounded slots are the alphabet of the gluing code. -/
lemma DefectRouteCertificate.tourPosition_card_le (c : DefectRouteCertificate s v) :
    Nat.card c.TourPosition ≤ 4*r := by
  classical
  have hlen := c.total_primitive_length_le
  have ht := c.tour_count_le_primitive_length
  have hsum := c.sum_tour_lengths
  simp only [Nat.card_eq_fintype_card,DefectRouteCertificate.TourPosition,
    Fintype.card_sigma,Fintype.card_fin,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one]
  omega

#print axioms finite_list_length_le_of_counts
#print axioms DefectRouteCertificate.total_primitive_length_le
#print axioms DefectRouteCertificate.sum_tour_lengths
#print axioms DefectRouteCertificate.tour_count_le_primitive_length
#print axioms DefectRouteCertificate.tourPosition_card_le
end SpectralRadiusUpperTail
