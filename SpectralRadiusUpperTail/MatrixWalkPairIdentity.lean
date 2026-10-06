import SpectralRadiusUpperTail.PairedSimpleWords
import SpectralRadiusUpperTail.SimpleWalkIdentity
import SpectralRadiusUpperTail.SharedWalkSupport

namespace SpectralRadiusUpperTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixWalk_simple_pair_eq (k : ℕ) (hk : 0 < k) (i j : ι) (v w : Fin k → ι)
    (hv : (i :: List.ofFn v).Nodup) (hw : (j :: List.ofFn w).Nodup)
    (hs : ∀ edge, entryMultiplicity (matrixWalkEdge i v) edge +
      entryMultiplicity (matrixWalkEdge j w) edge ≠ 1) : i = j ∧ v = w := by
  have he := pairedSimpleWords_images_eq (matrixWalkEdge i v) (matrixWalkEdge j w)
    (matrixWalkEdge_injective_of_nodup k i v hv)
    (matrixWalkEdge_injective_of_nodup k j w hw) hs
  have hle : listWalkEdges (i :: List.ofFn v) = listWalkEdges (j :: List.ofFn w) := by
    simpa only [matrixWalk_list_edges] using he
  have hl : i :: List.ofFn v = j :: List.ofFn w := by
    cases k with
    | zero => omega
    | succ m =>
      rw [List.ofFn_succ] at hv hle ⊢
      exact simpleWalk_eq_of_edges i (v 0) j _ _ hv hw hle
  exact ⟨(List.cons.inj hl).1, List.ofFn_injective (List.cons.inj hl).2⟩

open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- Complete finite paired-path structural dichotomy on the full visited
vertex type: at most k vertices, or two identical simple paths. -/
lemma iidMatrixWalk_structural_dichotomy (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (p q : ι → 𝕂)
    (k : ℕ) (hk : 0 < k) (i j : ι) (v w : Fin k → ι)
    (hcover : ∀ x, x ∈ i :: List.ofFn v ∨ x ∈ j :: List.ofFn w)
    (hn : (∫ x : ι × ι → 𝕂,
      matrixWalkTerm (Matrix.of (fun a b => x (a,b))) p k i v *
        star (matrixWalkTerm (Matrix.of (fun a b => x (a,b))) q k j w)
      ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0) :
    Fintype.card ι ≤ k ∨ (i = j ∧ v = w ∧ (i :: List.ofFn v).Nodup) := by
  by_cases hd : Disjoint (Finset.univ.image (matrixWalkEdge i v))
      (Finset.univ.image (matrixWalkEdge j w))
  · left
    have h := iidMatrixWalk_disjoint_vertex_count μ hm p q k hk i j v w hd hn
    have hu : (i :: List.ofFn v).toFinset ∪ (j :: List.ofFn w).toFinset = Finset.univ := by
      ext x
      simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_univ, iff_true]
      exact hcover x
    rwa [hu, Finset.card_univ] at h
  · obtain ⟨edge,he1,he2⟩ := Finset.not_disjoint_iff.mp hd
    have hc := (iidMatrixWalk_shared_support μ hm p q k i j v w edge he1 he2 hcover hn).1
    by_cases hsmall : Fintype.card ι ≤ k
    · exact Or.inl hsmall
    · have hmax : Fintype.card ι = k+1 := by omega
      have hsimp := iidMatrixWalk_shared_maximal_nodup μ hm p q k i j v w edge
        he1 he2 hcover hn hmax
      have hs : ∀ edge, entryMultiplicity (matrixWalkEdge i v) edge +
          entryMultiplicity (matrixWalkEdge j w) edge ≠ 1 := by
        intro edge he
        exact hn (iidMatrixWalk_singleton_zero μ hm p q k k i j v w edge he)
      have heq := matrixWalk_simple_pair_eq k hk i j v w hsimp.1 hsimp.2 hs
      exact Or.inr ⟨heq.1,heq.2,hsimp.1⟩

#print axioms matrixWalk_simple_pair_eq
#print axioms iidMatrixWalk_structural_dichotomy
end SpectralRadiusUpperTail
