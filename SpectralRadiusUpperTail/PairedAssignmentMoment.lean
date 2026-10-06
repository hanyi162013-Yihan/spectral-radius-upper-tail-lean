import SpectralRadiusUpperTail.PairedPatternWeight
import SpectralRadiusUpperTail.IidVertexRelabeling
import SpectralRadiusUpperTail.EqualityPatternSum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
variable {k n : ℕ}

lemma matrixWalkEdge_of_vertices {ι : Type*} (v : Fin (k+1) → ι) (a : Fin k) :
    matrixWalkEdge (v 0) (fun b : Fin k => v b.succ) a = (v a.castSucc,v a.succ) := by
  have hv : (Fin.cons (v 0) (fun b : Fin k => v b.succ) : Fin (k+1) → ι) = v := by
    funext b
    exact Fin.cases rfl (fun _ => rfl) b
  simp only [matrixWalkEdge,hv]

noncomputable def pairedAssignmentMoment (μ : Measure 𝕂)
    (x : (Fin (k+1) ⊕ Fin (k+1)) → Fin n) : 𝕂 :=
  ∫ y : Fin n × Fin n → 𝕂,
    (∏ a : Fin k, y (x (Sum.inl a.castSucc),x (Sum.inl a.succ)))*
    (∏ a : Fin k, star (y (x (Sum.inr a.castSucc),x (Sum.inr a.succ))))
    ∂Measure.pi (fun _ : Fin n × Fin n => μ)

noncomputable def pairedAssignmentWeight (p q : Fin n → 𝕂)
    (x : (Fin (k+1) ⊕ Fin (k+1)) → Fin n) : ℝ :=
  ‖p (x (Sum.inl 0))‖*‖q (x (Sum.inl (Fin.last k)))‖*
    ‖p (x (Sum.inr 0))‖*‖q (x (Sum.inr (Fin.last k)))‖

lemma pairedAssignmentMoment_relabel (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (r : Setoid (Fin (k+1) ⊕ Fin (k+1))) [DecidableRel r.r]
    (f : Quotient r → Fin n) (hf : Function.Injective f) :
    pairedAssignmentMoment μ (fun a => f (Quotient.mk r a)) = pairedPatternMoment μ r := by
  have h := iidPairedPath_relabel_expectation μ f hf k k
    (patternLeftVertex r 0) (patternRightVertex r 0)
    (fun a : Fin k => patternLeftVertex r a.succ)
    (fun a : Fin k => patternRightVertex r a.succ)
  have hL := matrixWalkEdge_of_vertices (patternLeftVertex r)
  have hR := matrixWalkEdge_of_vertices (patternRightVertex r)
  simp only [hL, hR] at h
  unfold pairedAssignmentMoment pairedPatternMoment
  simp only [hL, hR]
  exact h

lemma pairedAssignmentWeight_relabel
    (r : Setoid (Fin (k+1) ⊕ Fin (k+1))) (p q : Fin n → 𝕂) (f : Quotient r → Fin n) :
    pairedAssignmentWeight p q (fun a => f (Quotient.mk r a)) =
      pairedPatternEndpointWeight r p q f := rfl

#print axioms matrixWalkEdge_of_vertices
#print axioms pairedAssignmentMoment
#print axioms pairedAssignmentWeight
#print axioms pairedAssignmentMoment_relabel
#print axioms pairedAssignmentWeight_relabel
end SpectralRadiusUpperTail
