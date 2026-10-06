import SpectralRadiusUpperTail.GaussianBridgeModel

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma gaussianEntryBlock_norm_sq_integrable (d : ℕ) :
    Integrable (fun z : Fin d × Fin d → ℝ => ‖gaussianEntryBlock z‖^2)
      (Measure.pi (fun _ => standardNormal)) := by
  simp_rw [real_rectangular_frobenius_norm_sq]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    gaussian_coordinate_square_integrable (i,j)))

/-- Integrating independent Gaussian bridges successively gives the exact
product of diagonal-block energies. This calculation is in an explicit
product law; no conditional Schur-law identification is assumed. -/
theorem gaussianBridgeProduct_second_moment {d : ℕ} (t : ℝ) (l : ℕ)
    (D : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ) :
    Integrable (fun x : GaussianBridgeSpace d l => ‖gaussianBridgeProduct t l D x‖^2)
      (gaussianBridgeLaw d l) ∧
    (∫ x : GaussianBridgeSpace d l, ‖gaussianBridgeProduct t l D x‖^2 ∂gaussianBridgeLaw d l) =
      (t^2)^l * ∏ i, ‖D i‖^2 := by
  induction l with
  | zero =>
    change Integrable (fun _ : Unit => ‖D 0‖^2) (Measure.dirac ()) ∧
      (∫ _ : Unit, ‖D 0‖^2 ∂Measure.dirac ()) = (t^2)^0*∏ i : Fin 1, ‖D i‖^2
    constructor
    · exact integrable_const _
    · simp only [integral_const, probReal_univ, one_smul, pow_zero, one_mul,
        Fintype.prod_unique, Fin.default_eq_zero]
  | succ l ih =>
    have ih' := ih (fun i => D i.castSucc)
    have hg := gaussianEntryBlock_norm_sq_integrable d
    have henv := (ih'.1.mul_prod hg).const_mul (t^2*‖D (Fin.last (l+1))‖^2)
    have hf : Integrable (fun x : GaussianBridgeSpace d (l+1) =>
        ‖gaussianBridgeProduct t (l+1) D x‖^2) (gaussianBridgeLaw d (l+1)) := by
      apply henv.mono_nonneg (gaussianBridgeProduct_norm_sq_measurable t (l+1) D).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      exact Filter.Eventually.of_forall (fun x => matrix_sandwich_norm_sq_bound
        (gaussianBridgeProduct t l (fun i => D i.castSucc) x.1)
        (gaussianEntryBlock x.2) (D (Fin.last (l+1))) t)
    refine ⟨hf, ?_⟩
    change (∫ x : GaussianBridgeSpace d l × (Fin d × Fin d → ℝ),
      ‖gaussianBridgeProduct t l (fun i => D i.castSucc) x.1 *
        (t • gaussianEntryBlock x.2)*D (Fin.last (l+1))‖^2
      ∂(gaussianBridgeLaw d l).prod (Measure.pi (fun _ => standardNormal))) = _
    change Integrable (fun x : GaussianBridgeSpace d l × (Fin d × Fin d → ℝ) =>
      ‖gaussianBridgeProduct t l (fun i => D i.castSucc) x.1 *
        (t • gaussianEntryBlock x.2)*D (Fin.last (l+1))‖^2)
      ((gaussianBridgeLaw d l).prod (Measure.pi (fun _ => standardNormal))) at hf
    rw [integral_prod _ hf]
    simp_rw [(gaussian_scaled_sandwich_second_moment
      (gaussianBridgeProduct t l (fun i => D i.castSucc) _) (D (Fin.last (l+1))) t).2]
    rw [integral_mul_const, integral_const_mul, ih'.2]
    rw [Fin.prod_univ_castSucc (fun i : Fin (l+1+1) => ‖D i‖^2)]
    rw [pow_succ]
    ring

/-- At variance 1/n, each bridge contributes exactly the factor 1/n. -/
theorem gaussian_normalized_bridge_second_moment {d : ℕ} (n l : ℕ)
    (D : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ) :
    (∫ x : GaussianBridgeSpace d l,
      ‖gaussianBridgeProduct (1/Real.sqrt n) l D x‖^2 ∂gaussianBridgeLaw d l) =
      (1/(n : ℝ))^l * ∏ i, ‖D i‖^2 := by
  have hscale : (1/Real.sqrt n)^2 = 1/(n : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa only [hscale] using (gaussianBridgeProduct_second_moment (1/Real.sqrt n) l D).2

#print axioms gaussianBridgeProduct_second_moment
#print axioms gaussian_normalized_bridge_second_moment
end SpectralRadiusUpperTail
