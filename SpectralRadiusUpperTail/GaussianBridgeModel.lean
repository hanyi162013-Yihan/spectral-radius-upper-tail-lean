import SpectralRadiusUpperTail.GaussianScaledSandwich
import Mathlib.MeasureTheory.Integral.Prod

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

/-- A recursively grouped array of independent Gaussian off-diagonal
blocks. It is an explicit product model, not a claimed Schur decomposition. -/
def GaussianBridgeSpace (d : ℕ) : ℕ → Type
  | 0 => Unit
  | l+1 => GaussianBridgeSpace d l × (Fin d × Fin d → ℝ)

instance gaussianBridgeMeasurable (d : ℕ) : (l : ℕ) → MeasurableSpace (GaussianBridgeSpace d l)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | l+1 =>
    letI := gaussianBridgeMeasurable d l
    inferInstanceAs (MeasurableSpace (GaussianBridgeSpace d l × (Fin d × Fin d → ℝ)))

noncomputable def gaussianBridgeLaw (d : ℕ) : (l : ℕ) → Measure (GaussianBridgeSpace d l)
  | 0 => Measure.dirac ()
  | l+1 => (gaussianBridgeLaw d l).prod (Measure.pi (fun _ : Fin d × Fin d => standardNormal))

instance gaussianBridgeLaw_probability (d l : ℕ) : IsProbabilityMeasure (gaussianBridgeLaw d l) := by
  induction l with
  | zero => change IsProbabilityMeasure (Measure.dirac ()); infer_instance
  | succ l ih =>
    letI := ih
    change IsProbabilityMeasure ((gaussianBridgeLaw d l).prod
      (Measure.pi (fun _ : Fin d × Fin d => standardNormal)))
    infer_instance

/-- D0 N1 D1 ... Nl Dl, with each N scaled by t. -/
def gaussianBridgeProduct {d : ℕ} (t : ℝ) : (l : ℕ) →
    (Fin (l+1) → Matrix (Fin d) (Fin d) ℝ) → GaussianBridgeSpace d l → Matrix (Fin d) (Fin d) ℝ
  | 0, D, _ => D 0
  | l+1, D, x => gaussianBridgeProduct t l (fun i => D i.castSucc) x.1 *
      (t • gaussianEntryBlock x.2) * D (Fin.last (l+1))

lemma gaussianBridgeProduct_entry_measurable {d : ℕ} (t : ℝ) (l : ℕ)
    (D : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ) (a b : Fin d) :
    Measurable (fun x : GaussianBridgeSpace d l => gaussianBridgeProduct t l D x a b) := by
  induction l generalizing a b with
  | zero => exact measurable_const
  | succ l ih =>
    change Measurable (fun x : GaussianBridgeSpace d l × (Fin d × Fin d → ℝ) =>
      (gaussianBridgeProduct t l (fun i => D i.castSucc) x.1 *
        (t • gaussianEntryBlock x.2) * D (Fin.last (l+1))) a b)
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, gaussianEntryBlock]
    apply Finset.measurable_sum
    intro v _
    apply Measurable.mul_const
    apply Finset.measurable_sum
    intro u _
    have hx : Measurable (fun x : GaussianBridgeSpace d l × (Fin d × Fin d → ℝ) =>
        t*x.2 (u,v)) := by fun_prop
    exact ((ih _ a u).comp measurable_fst).mul hx

lemma gaussianBridgeProduct_norm_sq_measurable {d : ℕ} (t : ℝ) (l : ℕ)
    (D : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ) :
    Measurable (fun x : GaussianBridgeSpace d l => ‖gaussianBridgeProduct t l D x‖^2) := by
  simp_rw [real_rectangular_frobenius_norm_sq]
  exact Finset.measurable_sum _ (fun a _ => Finset.measurable_sum _ (fun b _ =>
    (gaussianBridgeProduct_entry_measurable t l D a b).pow_const 2))

#print axioms gaussianBridgeLaw_probability
#print axioms gaussianBridgeProduct_norm_sq_measurable
end SpectralRadiusUpperTail
