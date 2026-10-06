import SpectralRadiusUpperTail.SpectralWitness
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Instances.Matrix

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal NNReal
variable {n : ℕ}

instance finiteMatrixMeasurableSpace (m n : ℕ) (𝕜 : Type*) [MeasurableSpace 𝕜] :
    MeasurableSpace (Matrix (Fin m) (Fin n) 𝕜) :=
  inferInstanceAs (MeasurableSpace (Fin m → Fin n → 𝕜))

instance finiteMatrixBorelSpace (m n : ℕ) (𝕜 : Type*) [TopologicalSpace 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] [SecondCountableTopology 𝕜] :
    BorelSpace (Matrix (Fin m) (Fin n) 𝕜) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → 𝕜))

/-- Measurability is obtained from the proved Gelfand formula in mathlib. -/
theorem complex_spectralRadius_measurable :
    Measurable (fun A : Matrix (Fin n) (Fin n) ℂ => spectralRadius ℂ A) := by
  let : OpensMeasurableSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (OpensMeasurableSpace (Fin n → Fin n → ℂ))
  apply ENNReal.measurable_of_tendsto
    (f := fun k A => (‖A^k‖₊ : ℝ≥0∞) ^ (1 / k : ℝ))
  · intro k
    have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => ‖A^k‖₊) :=
      (continuous_id.pow k).nnnorm
    have hm : Measurable (fun A : Matrix (Fin n) (Fin n) ℂ => ‖A^k‖₊) := hc.measurable
    exact ENNReal.continuous_rpow_const.measurable.comp
      hm.coe_nnreal_ennreal
  · rw [tendsto_pi_nhds]
    exact fun A => spectrum.gelfand_formula A

theorem realMatrixRadius_measurable :
    Measurable (realMatrixRadius (n := n)) := by
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.map Complex.ofRealHom) :=
    continuous_id.matrix_map Complex.continuous_ofReal
  exact (complex_spectralRadius_measurable.comp hc.measurable).ennreal_toReal

lemma scaled_entryMatrix_continuous (c : ℝ) :
    Continuous (fun x : (Fin n × Fin n) → ℝ => c • entryMatrix x) := by
  apply continuous_matrix
  intro i j
  exact (continuous_apply (i,j)).const_smul c

theorem real_matrix_spectral_tail_measurable (c r : ℝ) :
    MeasurableSet {x : (Fin n × Fin n) → ℝ |
      r ≤ realMatrixRadius (c • entryMatrix x)} :=
  measurableSet_le measurable_const
    (realMatrixRadius_measurable.comp (scaled_entryMatrix_continuous c).measurable)

#print axioms complex_spectralRadius_measurable
#print axioms real_matrix_spectral_tail_measurable
end SpectralRadiusUpperTail
