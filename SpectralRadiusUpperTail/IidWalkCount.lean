import SpectralRadiusUpperTail.IidWordCount
import SpectralRadiusUpperTail.IidWalkSingleton

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι]
  [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- A nonzero actual paired-walk expectation can use at most half as many
 distinct directed edges as the total number of steps. -/
lemma iidMatrixWalk_nonzero_edge_count (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (q s : ι → 𝕂)
    (k l : ℕ) (i j : ι) (v : Fin k → ι) (w : Fin l → ι)
    (hn : (∫ x : ι × ι → 𝕂,
      matrixWalkTerm (Matrix.of (fun a b => x (a,b))) q k i v *
        star (matrixWalkTerm (Matrix.of (fun a b => x (a,b))) s l j w)
      ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0) :
    2 * (entryPairSupport (matrixWalkEdge i v) (matrixWalkEdge j w)).card ≤ k+l := by
  have hs : ∀ edge, entryMultiplicity (matrixWalkEdge i v) edge +
      entryMultiplicity (matrixWalkEdge j w) edge ≠ 1 := by
    intro edge he
    exact hn (iidMatrixWalk_singleton_zero μ hm q s k l i j v w edge he)
  simpa only [Fintype.card_fin] using
    entryPairSupport_card_le (matrixWalkEdge i v) (matrixWalkEdge j w) hs

/-- For two length-k walks, a nonzero paired contribution uses at most k
 distinct directed edges. This does not yet count vertex assignments. -/
lemma iidMatrixWalk_equal_length_edge_count (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (q s : ι → 𝕂)
    (k : ℕ) (i j : ι) (v w : Fin k → ι)
    (hn : (∫ x : ι × ι → 𝕂,
      matrixWalkTerm (Matrix.of (fun a b => x (a,b))) q k i v *
        star (matrixWalkTerm (Matrix.of (fun a b => x (a,b))) s k j w)
      ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0) :
    (entryPairSupport (matrixWalkEdge i v) (matrixWalkEdge j w)).card ≤ k := by
  have h := iidMatrixWalk_nonzero_edge_count μ hm q s k k i j v w hn
  omega

#print axioms iidMatrixWalk_nonzero_edge_count
#print axioms iidMatrixWalk_equal_length_edge_count
end SpectralRadiusUpperTail
