import SpectralRadiusUpperTail.GaussianSequentialCoupling
import SpectralRadiusUpperTail.GaussianRegressionMatrix

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- The fixed product of the explicit sequential row laws. Its intermediate
kernels remain available through gaussianSequentialRowLaw_succ. -/
noncomputable def gaussianSequentialMatrixLaw (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) : Measure (Fin N → Fin N → 𝕂 × 𝕂) :=
  Measure.pi (fun i => gaussianSequentialRowLaw μ v a N (t i) N)

lemma gaussianSequentialMatrixLaw_probability (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (t : Fin N → 𝕂) :
    IsProbabilityMeasure (gaussianSequentialMatrixLaw μ v a t) := by
  have (i : Fin N) : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N (t i) N) :=
    gaussianSequentialRowLaw_probability μ v a ha N (t i) N
  unfold gaussianSequentialMatrixLaw
  infer_instance

lemma gaussianSequentialMatrixLaw_source (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a : ℝ) (ha : 0 < a) (t : Fin N → 𝕂) :
    (gaussianSequentialMatrixLaw μ v a t).map
        (fun x i => coordinateVector Prod.fst N (x i)) = gaussianTiltedMatrixLaw μ a v t := by
  have (i : Fin N) : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N (t i) N) :=
    gaussianSequentialRowLaw_probability μ v a ha N (t i) N
  have hfst := measurable_coordinateVector (@Prod.fst 𝕂 𝕂) measurable_fst N
  have (i : Fin N) : IsProbabilityMeasure
      ((gaussianSequentialRowLaw μ v a N (t i) N).map (coordinateVector Prod.fst N)) :=
    Measure.isProbabilityMeasure_map hfst.aemeasurable
  unfold gaussianSequentialMatrixLaw gaussianTiltedMatrixLaw
  rw [Measure.pi_map_pi (fun _ => hfst.aemeasurable)]
  congr 1
  funext i
  exact gaussianSequentialRowLaw_source μ hX hm hvar v N hv a ha (t i)

lemma gaussianSequentialMatrixLaw_comparator (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (t : Fin N → 𝕂) :
    (gaussianSequentialMatrixLaw μ v a t).map (fun x i => comparatorVector N (x i)) =
      Measure.pi (fun _ : Fin N => Measure.pi (fun _ : Fin N => μ)) := by
  have (i : Fin N) : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N (t i) N) :=
    gaussianSequentialRowLaw_probability μ v a ha N (t i) N
  have hsnd := measurable_comparatorVector (α := 𝕂) N
  have (i : Fin N) : IsProbabilityMeasure
      ((gaussianSequentialRowLaw μ v a N (t i) N).map (comparatorVector N)) :=
    Measure.isProbabilityMeasure_map hsnd.aemeasurable
  unfold gaussianSequentialMatrixLaw
  rw [Measure.pi_map_pi (fun _ => hsnd.aemeasurable)]
  congr 1
  funext i
  exact gaussianSequentialRowLaw_comparator μ v a ha N (t i) N

#print axioms gaussianSequentialMatrixLaw_source
#print axioms gaussianSequentialMatrixLaw_comparator
end SpectralRadiusUpperTail
