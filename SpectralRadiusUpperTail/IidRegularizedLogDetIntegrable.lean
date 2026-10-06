import SpectralRadiusUpperTail.SpectralMeasurable
import SpectralRadiusUpperTail.MatrixRegularizedLogDet
import SpectralRadiusUpperTail.RegularizedLogDetUpper
import SpectralRadiusUpperTail.IntegrableShiftedSquare
import SpectralRadiusUpperTail.IidNormalizedGramMoment
import SpectralRadiusUpperTail.FrobeniusTraceIdentity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix.Norms.Frobenius ComplexOrder MatrixOrder

lemma normalizedIidMatrix_continuous (n : ℕ) :
    Continuous (fun x : Fin n × Fin n → ℂ => normalizedIidMatrix x) := by
  unfold normalizedIidMatrix
  fun_prop

lemma matrixRegularizedLogDet_measurable (n : ℕ) (b s : ℝ) :
    Measurable (fun A : Matrix (Fin n) (Fin n) ℂ => matrixRegularizedLogDet A b s) := by
  unfold matrixRegularizedLogDet
  have hh : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ =>
      (((A-(b : ℂ) • 1).conjTranspose*(A-(b : ℂ) • 1))+(s : ℂ) • 1).det) := by
    fun_prop
  exact Real.measurable_log.comp hh.norm.measurable

/-- The norm in this bound is the Frobenius norm. -/
lemma matrixRegularizedLogDet_upper_energy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b s : ℝ) (hs : 0 < s) :
    matrixRegularizedLogDet A b s ≤ ‖A-(b : ℂ) • 1‖^2+(n : ℝ)*s := by
  have hh := posSemidef_shift_logDet_upper _
    (Matrix.posSemidef_conjTranspose_mul_self (A-(b : ℂ) • 1)) s hs
  rw [Matrix.trace_mul_comm, ← frobenius_norm_sq_trace] at hh
  exact hh

lemma iidRegularizedLogDet_integrable (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (n : ℕ) (b s : ℝ) (hs : 0 < s) :
    Integrable (fun x : Fin n × Fin n → ℂ => matrixRegularizedLogDet (normalizedIidMatrix x) b s)
      (Measure.pi (fun _ => μ)) := by
  have h2 : Integrable (fun x : Fin n × Fin n → ℂ => ‖normalizedIidMatrix x‖^2)
      (Measure.pi (fun _ => μ)) := by
    have hh := normalizedGramTraceMoment_integrable μ c hc hexp 1 1 n
    simpa only [pow_one, matrixTraceMoment, ← frobenius_norm_sq_trace] using hh
  have hshift := integrable_shifted_norm_sq _ _
    ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
    (((normalizedIidMatrix_continuous n).sub continuous_const).norm.pow 2).measurable h2
  have hmeas := (matrixRegularizedLogDet_measurable n b s).comp (normalizedIidMatrix_continuous n).measurable
  apply (((integrable_const |(n : ℝ)*Real.log s|).add hshift).add
    (integrable_const ((n : ℝ)*s))).mono' hmeas.aestronglyMeasurable
  filter_upwards with x
  change ‖matrixRegularizedLogDet (normalizedIidMatrix x) b s‖ ≤
    |(n : ℝ)*Real.log s|+‖normalizedIidMatrix x-(b : ℂ) • 1‖^2+(n : ℝ)*s
  rw [Real.norm_eq_abs, abs_le]
  have hl := matrixRegularizedLogDet_floor (normalizedIidMatrix x) b s hs
  have hu := matrixRegularizedLogDet_upper_energy (normalizedIidMatrix x) b s hs
  have henergy := sq_nonneg ‖normalizedIidMatrix x-(b : ℂ) • 1‖
  have hns : 0 ≤ (n : ℝ)*s := mul_nonneg (Nat.cast_nonneg n) hs.le
  constructor
  · linarith [neg_abs_le ((n : ℝ)*Real.log s)]
  · linarith [abs_nonneg ((n : ℝ)*Real.log s)]

#print axioms normalizedIidMatrix_continuous
#print axioms matrixRegularizedLogDet_measurable
#print axioms matrixRegularizedLogDet_upper_energy
#print axioms iidRegularizedLogDet_integrable
end SpectralRadiusUpperTail
