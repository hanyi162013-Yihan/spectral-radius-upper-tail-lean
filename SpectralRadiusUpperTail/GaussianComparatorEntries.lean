import SpectralRadiusUpperTail.GaussianSequentialMatrix
import SpectralRadiusUpperTail.ActualMatrixIdentity
import SpectralRadiusUpperTail.IidMatrixFlatten
import SpectralRadiusUpperTail.IidNormalizedGramMoment
import SpectralRadiusUpperTail.MapEventProbability

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {n : ℕ}

def gaussianComparatorEntries (x : Fin n → Fin n → 𝕂 × 𝕂) (ij : Fin n × Fin n) : 𝕂 :=
  comparatorVector n (x ij.1) ij.2

lemma measurable_gaussianComparatorEntries : Measurable (gaussianComparatorEntries (𝕂 := 𝕂) (n := n)) := by
  apply measurable_pi_lambda
  intro ij
  exact (measurable_pi_apply ij.2).comp
    ((measurable_comparatorVector (α := 𝕂) n).comp (measurable_pi_apply ij.1))

lemma gaussianComparatorEntries_law (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (t : Fin n → 𝕂) :
    (gaussianSequentialMatrixLaw μ v a t).map gaussianComparatorEntries =
      Measure.pi (fun _ : Fin n × Fin n => μ) := by
  have hf : Measurable (fun x : Fin n → Fin n → 𝕂 × 𝕂 => fun i => comparatorVector n (x i)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_comparatorVector (α := 𝕂) n).comp (measurable_pi_apply i))
  have hg : Measurable (fun x : Fin n → Fin n → 𝕂 => fun ij : Fin n × Fin n => x ij.1 ij.2) := by
    fun_prop
  rw [← iid_matrix_flatten_law μ n,← gaussianSequentialMatrixLaw_comparator μ v a ha t,
    Measure.map_map hg hf]
  rfl

lemma normalized_gaussianComparatorEntries (x : Fin n → Fin n → 𝕂 × 𝕂) :
    normalizedIidMatrix (gaussianComparatorEntries x) =
      normalizedArray (fun i => comparatorVector n (x i)) := by
  ext i j
  simp only [normalizedIidMatrix,normalizedArray,Matrix.smul_apply,Matrix.of_apply,
    RCLike.real_smul_eq_coe_mul,smul_eq_mul,gaussianComparatorEntries]

lemma gaussianComparator_event_probability_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (t : Fin n → 𝕂)
    (P : Matrix (Fin n) (Fin n) 𝕂 → Prop) :
    (gaussianSequentialMatrixLaw μ v a t).real
      {x | P (normalizedArray (fun i => comparatorVector n (x i)))} ≤
    (Measure.pi (fun _ : Fin n × Fin n => μ)).real {x | P (normalizedIidMatrix x)} := by
  letI := gaussianSequentialMatrixLaw_probability μ v a ha t
  have hh := event_probability_le_of_map (gaussianSequentialMatrixLaw μ v a t)
    (Measure.pi (fun _ : Fin n × Fin n => μ)) gaussianComparatorEntries
    measurable_gaussianComparatorEntries.aemeasurable (gaussianComparatorEntries_law μ v a ha t)
    {x | P (normalizedIidMatrix x)}
  simpa only [Set.preimage_setOf_eq,normalized_gaussianComparatorEntries] using hh

#print axioms gaussianComparatorEntries
#print axioms measurable_gaussianComparatorEntries
#print axioms gaussianComparatorEntries_law
#print axioms normalized_gaussianComparatorEntries
#print axioms gaussianComparator_event_probability_le
end SpectralRadiusUpperTail
