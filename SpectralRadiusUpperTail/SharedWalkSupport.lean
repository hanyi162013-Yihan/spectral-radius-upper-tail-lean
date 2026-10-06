import SpectralRadiusUpperTail.WalkSupportOrientation
import SpectralRadiusUpperTail.MatrixWalkSimple
import SpectralRadiusUpperTail.IidWalkCount
import SpectralRadiusUpperTail.ListOrientedTree

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι]
  [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- A shared-edge paired contribution on its full visited vertex type has
at most k+1 vertices. The extremal case is an oriented tree. -/
lemma iidMatrixWalk_shared_support (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (p q : ι → 𝕂)
    (k : ℕ) (i j : ι) (v w : Fin k → ι) (edge : ι × ι)
    (he1 : edge ∈ Finset.univ.image (matrixWalkEdge i v))
    (he2 : edge ∈ Finset.univ.image (matrixWalkEdge j w))
    (hcover : ∀ x, x ∈ i :: List.ofFn v ∨ x ∈ j :: List.ofFn w)
    (hn : (∫ x : ι × ι → 𝕂,
      matrixWalkTerm (Matrix.of (fun a b => x (a,b))) p k i v *
        star (matrixWalkTerm (Matrix.of (fun a b => x (a,b))) q k j w)
      ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0) :
    let E := Finset.univ.image (matrixWalkEdge i v) ∪ Finset.univ.image (matrixWalkEdge j w)
    Fintype.card ι ≤ k+1 ∧ (Fintype.card ι = k+1 →
      (walkSupportGraph E).IsTree ∧ (∀ a b, (a,b) ∈ E → a ≠ b) ∧
        (∀ a b, (a,b) ∈ E → (b,a) ∉ E)) := by
  let E := Finset.univ.image (matrixWalkEdge i v) ∪ Finset.univ.image (matrixWalkEdge j w)
  have hc : (walkSupportGraph E).Connected := by
    have h1 : edge ∈ listWalkEdges (i :: List.ofFn v) := by
      rwa [matrixWalk_list_edges]
    have h2 : edge ∈ listWalkEdges (j :: List.ofFn w) := by
      rwa [matrixWalk_list_edges]
    simpa only [matrixWalk_list_edges] using
      pairedWalk_support_connected (i :: List.ofFn v) (j :: List.ofFn w) edge h1 h2 hcover
  have hE : E.card ≤ k := by
    have h := iidMatrixWalk_equal_length_edge_count μ hm p q k i j v w hn
    simpa only [entryPairSupport_eq_images] using h
  have hv := walkSupportGraph_vertex_card_le E hc
  constructor
  · omega
  · intro hmax
    apply walkSupportGraph_oriented_tree E hc
    omega

/-- In the extremal shared-edge case, both actual matrix walks are simple. -/
lemma iidMatrixWalk_shared_maximal_nodup (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (p q : ι → 𝕂)
    (k : ℕ) (i j : ι) (v w : Fin k → ι) (edge : ι × ι)
    (he1 : edge ∈ Finset.univ.image (matrixWalkEdge i v))
    (he2 : edge ∈ Finset.univ.image (matrixWalkEdge j w))
    (hcover : ∀ x, x ∈ i :: List.ofFn v ∨ x ∈ j :: List.ofFn w)
    (hn : (∫ x : ι × ι → 𝕂,
      matrixWalkTerm (Matrix.of (fun a b => x (a,b))) p k i v *
        star (matrixWalkTerm (Matrix.of (fun a b => x (a,b))) q k j w)
      ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0)
    (hmax : Fintype.card ι = k+1) :
    (i :: List.ofFn v).Nodup ∧ (j :: List.ofFn w).Nodup := by
  let E := Finset.univ.image (matrixWalkEdge i v) ∪ Finset.univ.image (matrixWalkEdge j w)
  have h := (iidMatrixWalk_shared_support μ hm p q k i j v w edge he1 he2 hcover hn).2 hmax
  constructor
  · apply listWalk_nodup_of_oriented_tree E h.1 h.2.1 h.2.2
    rw [matrixWalk_list_edges]
    exact Finset.subset_union_left
  · apply listWalk_nodup_of_oriented_tree E h.1 h.2.1 h.2.2
    rw [matrixWalk_list_edges]
    exact Finset.subset_union_right

#print axioms iidMatrixWalk_shared_support
#print axioms iidMatrixWalk_shared_maximal_nodup
end SpectralRadiusUpperTail
