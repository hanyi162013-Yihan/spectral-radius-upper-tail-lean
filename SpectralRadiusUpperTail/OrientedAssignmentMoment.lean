import SpectralRadiusUpperTail.IidVertexRelabeling
import SpectralRadiusUpperTail.CanonicalWalkDefectMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {V U 𝕂 : Type*} [Fintype V] [Fintype U]
  [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {n : ℕ}

noncomputable def orientedAssignmentMoment (μ : Measure 𝕂) (s : Fin n → Bool)
    (v : Fin (n+1) → V) : 𝕂 :=
  ∫ x : V × V → 𝕂, (∏ a, if s a then star (x (orientedWalkEdge s v a))
    else x (orientedWalkEdge s v a)) ∂Measure.pi (fun _ : V × V => μ)

lemma orientedWalkEdge_map (s : Fin n → Bool) (v : Fin (n+1) → V) (f : V → U) (i : Fin n) :
    orientedWalkEdge s (f ∘ v) i = (f (orientedWalkEdge s v i).1,f (orientedWalkEdge s v i).2) := by
  cases h : s i <;> simp [orientedWalkEdge,h,Function.comp_def]

/-- Signed iid moments are invariant under injective vertex assignments; this
uses only the iid coordinate law, not a reversal of the original sign word. -/
lemma orientedAssignmentMoment_relabel (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (s : Fin n → Bool) (v : Fin (n+1) → V) (f : V → U) (hf : Function.Injective f) :
    orientedAssignmentMoment μ s (f ∘ v) = orientedAssignmentMoment μ s v := by
  unfold orientedAssignmentMoment
  simp_rw [orientedWalkEdge_map]
  exact iidIndexEmbedding_integral μ (fun e : V × V => (f e.1,f e.2))
    (vertexPairMap_injective f hf)
    (fun x => ∏ a, if s a then star (x (orientedWalkEdge s v a)) else x (orientedWalkEdge s v a))
    (by
      apply Continuous.aestronglyMeasurable
      apply continuous_finset_prod
      intro a _
      cases h : s a <;> simp only [h,Bool.false_eq_true,if_false,if_true] <;> fun_prop)

lemma orientedPatternMoment_relabel {r : ℕ} (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (s : Fin (2*r) → Bool) (R : Setoid (Fin (2*r+1))) [DecidableRel R.r]
    (f : Quotient R → U) (hf : Function.Injective f) :
    orientedAssignmentMoment μ s (fun a => f (Quotient.mk R a)) = orientedPatternMoment μ s R :=
  orientedAssignmentMoment_relabel μ s (Quotient.mk R) f hf

#print axioms orientedAssignmentMoment
#print axioms orientedWalkEdge_map
#print axioms orientedAssignmentMoment_relabel
#print axioms orientedPatternMoment_relabel
end SpectralRadiusUpperTail
