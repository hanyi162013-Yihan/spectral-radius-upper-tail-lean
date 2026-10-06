import SpectralRadiusUpperTail.IidEmbeddingIntegral
import SpectralRadiusUpperTail.IidWalkSingleton

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {σ τ 𝕂 : Type*} [Fintype σ] [Fintype τ]
  [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- Injective vertex relabeling preserves injectivity of directed entry indices. -/
lemma vertexPairMap_injective (f : τ → σ) (hf : Function.Injective f) :
    Function.Injective (fun e : τ × τ => (f e.1,f e.2)) := by
  intro a b h
  exact Prod.ext (hf (congrArg Prod.fst h)) (hf (congrArg Prod.snd h))

/-- The actual iid edge-product moment of two paths depends only on their
 equality pattern, not on the injective vertex labels used to realize it. -/
lemma iidPairedPath_relabel_expectation (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (f : τ → σ) (hf : Function.Injective f)
    (k l : ℕ) (i j : τ) (v : Fin k → τ) (w : Fin l → τ) :
    (∫ x : σ × σ → 𝕂,
      (∏ a, x (f (matrixWalkEdge i v a).1,f (matrixWalkEdge i v a).2))*
      (∏ b, star (x (f (matrixWalkEdge j w b).1,f (matrixWalkEdge j w b).2)))
      ∂Measure.pi (fun _ : σ × σ => μ)) =
    (∫ y : τ × τ → 𝕂, (∏ a, y (matrixWalkEdge i v a))*
      (∏ b, star (y (matrixWalkEdge j w b)))
      ∂Measure.pi (fun _ : τ × τ => μ)) :=
  iidWordPair_embedding_expectation μ (fun e : τ × τ => (f e.1,f e.2))
    (vertexPairMap_injective f hf) (matrixWalkEdge i v) (matrixWalkEdge j w)

#print axioms vertexPairMap_injective
#print axioms iidPairedPath_relabel_expectation
end SpectralRadiusUpperTail
