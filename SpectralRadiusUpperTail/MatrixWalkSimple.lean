import SpectralRadiusUpperTail.MatrixWalkList
import SpectralRadiusUpperTail.IidWordSupport
import Mathlib.Data.List.FinRange

namespace SpectralRadiusUpperTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixWalkEdge_injective_of_nodup (k : ℕ) (i : ι) (v : Fin k → ι)
    (h : (i :: List.ofFn v).Nodup) : Function.Injective (matrixWalkEdge i v) := by
  have hl : List.ofFn (Fin.cons i v : Fin (k+1) → ι) = i :: List.ofFn v := by
    simp [List.ofFn_succ]
  have hf : Function.Injective (Fin.cons i v : Fin (k+1) → ι) :=
    List.nodup_ofFn.mp (hl.symm ▸ h)
  intro a b hab
  apply Fin.castSucc_injective
  apply hf
  exact congrArg Prod.fst hab

/-- With disjoint directed edges and no singletons, each nonempty walk must
revisit a vertex. -/
lemma matrixWalk_disjoint_not_nodup (k l : ℕ) (hk : 0 < k)
    (i j : ι) (v : Fin k → ι) (w : Fin l → ι)
    (hd : Disjoint (Finset.univ.image (matrixWalkEdge i v))
      (Finset.univ.image (matrixWalkEdge j w)))
    (hs : ∀ edge, entryMultiplicity (matrixWalkEdge i v) edge +
      entryMultiplicity (matrixWalkEdge j w) edge ≠ 1) :
    ¬(i :: List.ofFn v).Nodup := by
  intro hn
  let a : Fin k := ⟨0,hk⟩
  have he := entryMultiplicity_of_injective (matrixWalkEdge i v)
    (matrixWalkEdge_injective_of_nodup k i v hn) a
  have hz : entryMultiplicity (matrixWalkEdge j w) (matrixWalkEdge i v a) = 0 := by
    have hp : ¬0 < entryMultiplicity (matrixWalkEdge j w) (matrixWalkEdge i v a) := by
      rw [entryMultiplicity_pos_iff]
      rintro ⟨b,hb⟩
      exact Finset.disjoint_left.mp hd
        (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
        (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,hb⟩)
    omega
  exact hs (matrixWalkEdge i v a) (by omega)

/-- The disjoint-edge case has no extra free vertex in either walk. -/
lemma matrixWalk_disjoint_vertex_count (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (i j : ι) (v : Fin k → ι) (w : Fin l → ι)
    (hd : Disjoint (Finset.univ.image (matrixWalkEdge i v))
      (Finset.univ.image (matrixWalkEdge j w)))
    (hs : ∀ edge, entryMultiplicity (matrixWalkEdge i v) edge +
      entryMultiplicity (matrixWalkEdge j w) edge ≠ 1) :
    2 * ((i :: List.ofFn v).toFinset.card + (j :: List.ofFn w).toFinset.card) ≤ k+l := by
  have hv := (matrixWalk_vertex_count k i v).2
    (matrixWalk_disjoint_not_nodup k l hk i j v w hd hs)
  have hw := (matrixWalk_vertex_count l j w).2
    (matrixWalk_disjoint_not_nodup l k hl j i w v hd.symm (by
      intro edge
      simpa only [Nat.add_comm] using hs edge))
  have hc := entryPairSupport_card_le (matrixWalkEdge i v) (matrixWalkEdge j w) hs
  rw [entryPairSupport_eq_images, Finset.card_union_of_disjoint hd] at hc
  simp only [Fintype.card_fin] at hc
  omega

open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- For an actual nonzero iid paired contribution with no common directed
 edge, the union of vertices has at most k elements. -/
lemma iidMatrixWalk_disjoint_vertex_count (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (p q : ι → 𝕂)
    (k : ℕ) (hk : 0 < k) (i j : ι) (v w : Fin k → ι)
    (hd : Disjoint (Finset.univ.image (matrixWalkEdge i v))
      (Finset.univ.image (matrixWalkEdge j w)))
    (hn : (∫ x : ι × ι → 𝕂,
      matrixWalkTerm (Matrix.of (fun a b => x (a,b))) p k i v *
        star (matrixWalkTerm (Matrix.of (fun a b => x (a,b))) q k j w)
      ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0) :
    ((i :: List.ofFn v).toFinset ∪ (j :: List.ofFn w).toFinset).card ≤ k := by
  have hs : ∀ edge, entryMultiplicity (matrixWalkEdge i v) edge +
      entryMultiplicity (matrixWalkEdge j w) edge ≠ 1 := by
    intro edge he
    exact hn (iidMatrixWalk_singleton_zero μ hm p q k k i j v w edge he)
  have h := matrixWalk_disjoint_vertex_count k k hk hk i j v w hd hs
  have hu := Finset.card_union_le (i :: List.ofFn v).toFinset (j :: List.ofFn w).toFinset
  omega

#print axioms matrixWalkEdge_injective_of_nodup
#print axioms matrixWalk_disjoint_not_nodup
#print axioms matrixWalk_disjoint_vertex_count
#print axioms iidMatrixWalk_disjoint_vertex_count
end SpectralRadiusUpperTail
