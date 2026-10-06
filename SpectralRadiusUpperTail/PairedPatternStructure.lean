import SpectralRadiusUpperTail.PairedPatternVertices
import SpectralRadiusUpperTail.MatrixWalkPairIdentity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
variable {k : ℕ}

/-- The unweighted iid paired-edge moment attached to one equality pattern. -/
noncomputable def pairedPatternMoment (μ : Measure 𝕂)
    (r : Setoid (Fin (k+1) ⊕ Fin (k+1))) [DecidableRel r.r] : 𝕂 :=
  ∫ y : Quotient r × Quotient r → 𝕂,
    (∏ a : Fin k, y (matrixWalkEdge (patternLeftVertex r 0)
      (fun b : Fin k => patternLeftVertex r b.succ) a))*
    (∏ a : Fin k, star (y (matrixWalkEdge (patternRightVertex r 0)
      (fun b : Fin k => patternRightVertex r b.succ) a)))
    ∂Measure.pi (fun _ : Quotient r × Quotient r => μ)

/-- The finite structural dichotomy instantiated on the actual quotient
paths; vertex coverage is proved internally. -/
lemma pairedPattern_nonzero_structure (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hk : 0 < k)
    (r : Setoid (Fin (k+1) ⊕ Fin (k+1))) [DecidableRel r.r]
    (hn : pairedPatternMoment μ r ≠ 0) :
    Fintype.card (Quotient r) ≤ k ∨
      (patternLeftVertex r 0 = patternRightVertex r 0 ∧
        (fun a : Fin k => patternLeftVertex r a.succ) =
          (fun a : Fin k => patternRightVertex r a.succ) ∧
        (patternLeftVertex r 0 :: List.ofFn (fun a : Fin k => patternLeftVertex r a.succ)).Nodup) := by
  apply iidMatrixWalk_structural_dichotomy μ hm (fun _ => (1 : 𝕂)) (fun _ => (1 : 𝕂))
    k hk (patternLeftVertex r 0) (patternRightVertex r 0)
    (fun a : Fin k => patternLeftVertex r a.succ)
    (fun a : Fin k => patternRightVertex r a.succ)
    (pairedPattern_vertex_cover r)
  simpa only [matrixWalkTerm_product, mul_one, star_mul, star_one, star_prod,
    Matrix.of_apply, matrixWalkEdge, pairedPatternMoment] using hn

#print axioms pairedPatternMoment
#print axioms pairedPattern_nonzero_structure
end SpectralRadiusUpperTail
