import SpectralRadiusUpperTail.GaussianBridgeMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma gaussianBridgeProduct_parametric_entry_measurable {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (t : ℝ) (l : ℕ)
    (D : Fin (l+1) → Ω → Matrix (Fin d) (Fin d) ℝ)
    (X : Ω → GaussianBridgeSpace d l) (hX : Measurable X)
    (hD : ∀ i a b, Measurable (fun s => D i s a b)) (a b : Fin d) :
    Measurable (fun s => gaussianBridgeProduct t l (fun i => D i s) (X s) a b) := by
  induction l generalizing a b with
  | zero => exact hD 0 a b
  | succ l ih =>
    change Measurable (fun s =>
      (gaussianBridgeProduct t l (fun i => D i.castSucc s) (X s).1 *
        (t • gaussianEntryBlock (X s).2) * D (Fin.last (l+1)) s) a b)
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, gaussianEntryBlock]
    apply Finset.measurable_sum
    intro v _
    apply Measurable.mul _ (hD _ _ _)
    apply Finset.measurable_sum
    intro u _
    exact (ih (fun i => D i.castSucc) (fun s => (X s).1) hX.fst
      (fun i => hD i.castSucc) a u).mul
      (((measurable_pi_apply (u,v)).comp hX.snd).const_mul t)

lemma gaussianBridgeProduct_parametric_norm_measurable {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (t : ℝ) (l : ℕ)
    (D : Fin (l+1) → Ω → Matrix (Fin d) (Fin d) ℝ)
    (X : Ω → GaussianBridgeSpace d l) (hX : Measurable X)
    (hD : ∀ i a b, Measurable (fun s => D i s a b)) :
    Measurable (fun s => ‖gaussianBridgeProduct t l (fun i => D i s) (X s)‖^2) := by
  simp_rw [real_rectangular_frobenius_norm_sq]
  exact Finset.measurable_sum _ (fun a _ => Finset.measurable_sum _ (fun b _ =>
    (gaussianBridgeProduct_parametric_entry_measurable t l D X hX hD a b).pow_const 2))

/-- Gaussian bridges can be integrated out while retaining a possibly
random diagonal array, independent of the bridges. Diagonal blocks are
not required to be independent for this identity. -/
theorem gaussian_bridge_random_diagonal_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {d : ℕ} (t : ℝ) (l : ℕ)
    (D : Fin (l+1) → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hD : ∀ i a b, Measurable (fun s => D i s a b))
    (hi : Integrable (fun s => ∏ i, ‖D i s‖^2) μ) :
    Integrable (fun z : Ω × GaussianBridgeSpace d l =>
      ‖gaussianBridgeProduct t l (fun i => D i z.1) z.2‖^2) (μ.prod (gaussianBridgeLaw d l)) ∧
    (∫ z : Ω × GaussianBridgeSpace d l,
      ‖gaussianBridgeProduct t l (fun i => D i z.1) z.2‖^2 ∂μ.prod (gaussianBridgeLaw d l)) =
      (t^2)^l*(∫ s, ∏ i, ‖D i s‖^2 ∂μ) := by
  have hm := gaussianBridgeProduct_parametric_norm_measurable t l
    (fun i (z : Ω × GaussianBridgeSpace d l) => D i z.1) Prod.snd measurable_snd
    (fun i a b => (hD i a b).comp measurable_fst)
  have hf : Integrable (fun z : Ω × GaussianBridgeSpace d l =>
      ‖gaussianBridgeProduct t l (fun i => D i z.1) z.2‖^2) (μ.prod (gaussianBridgeLaw d l)) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall (fun s => (gaussianBridgeProduct_second_moment t l (fun i => D i s)).1)
    · simp only [Real.norm_of_nonneg (sq_nonneg _)]
      simp_rw [(gaussianBridgeProduct_second_moment t l (fun i => D i _)).2]
      exact hi.const_mul _
  refine ⟨hf, ?_⟩
  rw [integral_prod _ hf]
  simp_rw [(gaussianBridgeProduct_second_moment t l (fun i => D i _)).2]
  exact integral_const_mul _ _

#print axioms gaussian_bridge_random_diagonal_moment
end SpectralRadiusUpperTail
