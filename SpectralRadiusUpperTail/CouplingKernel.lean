import SpectralRadiusUpperTail.DensityCoupling
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MapComap

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Θ α : Type*} [MeasurableSpace Θ] [MeasurableSpace α]

lemma measurable_parameter_withDensity (μ : Measure α) [SFinite μ]
    (k : Θ → α → ℝ≥0∞) (hk : Measurable (Function.uncurry k)) :
    Measurable (fun s => μ.withDensity (k s)) := by
  have h := (Kernel.withDensity (Kernel.const Θ μ) k).measurable
  have heq : (fun s => Kernel.withDensity (Kernel.const Θ μ) k s) =
      (fun s => μ.withDensity (k s)) := by
    funext s
    rw [Kernel.withDensity_apply _ hk]
    rfl
  change Measurable (fun s => Kernel.withDensity (Kernel.const Θ μ) k s) at h
  rwa [heq] at h

/-- Joint measurability of the explicit common-part coupling, including
parameters where the residual mass is zero. -/
theorem densityCoupling_measurable (μ : Measure α) [SFinite μ]
    (k : Θ → α → ℝ≥0∞) (hk : Measurable (Function.uncurry k)) :
    Measurable (fun s => densityCoupling μ (k s)) := by
  have hcommon : Measurable (fun s => commonDensityPart μ (k s)) :=
    measurable_parameter_withDensity μ (fun s x => min (k s x) 1)
      (hk.min measurable_const)
  have hpos : Measurable (fun s => positiveDensityResidual μ (k s)) :=
    measurable_parameter_withDensity μ (fun s x => k s x - min (k s x) 1)
      (hk.sub (hk.min measurable_const))
  have hleft : Measurable (fun z : Θ × (α × α) => k z.1 z.2.1) :=
    hk.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hright : Measurable (fun z : Θ × (α × α) => k z.1 z.2.2) :=
    hk.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hprod : Measurable (fun s =>
      (positiveDensityResidual μ (k s)).prod (negativeDensityResidual μ (k s))) := by
    have h := measurable_parameter_withDensity (μ.prod μ)
      (fun s z => (k s z.1 - min (k s z.1) 1) * (1 - min (k s z.2) 1))
      ((hleft.sub (hleft.min measurable_const)).mul
        (measurable_const.sub (hright.min measurable_const)))
    have heq : (fun s => (μ.prod μ).withDensity
          (fun z => (k s z.1 - min (k s z.1) 1) * (1 - min (k s z.2) 1))) =
        (fun s => (positiveDensityResidual μ (k s)).prod
          (negativeDensityResidual μ (k s))) := by
      funext s
      exact (prod_withDensity
        (hk.of_uncurry_left.sub (hk.of_uncurry_left.min measurable_const))
        (measurable_const.sub (hk.of_uncurry_left.min measurable_const))).symm
    rwa [heq] at h
  have hmass : Measurable (fun s => positiveDensityResidual μ (k s) Set.univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp hpos
  have hres : Measurable (fun s => (positiveDensityResidual μ (k s) Set.univ)⁻¹ •
      (positiveDensityResidual μ (k s)).prod (negativeDensityResidual μ (k s))) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.smul_apply, smul_eq_mul]
    exact hmass.inv.mul ((Measure.measurable_coe hA).comp hprod)
  exact ((Measure.measurable_map (fun x : α => (x,x))
    (measurable_id.prodMk measurable_id)).comp hcommon).add hres

noncomputable def densityCouplingKernel (μ : Measure α) [SFinite μ]
    (k : Θ → α → ℝ≥0∞) (hk : Measurable (Function.uncurry k)) : Kernel Θ (α × α) :=
  ⟨fun s => densityCoupling μ (k s), densityCoupling_measurable μ k hk⟩

theorem densityCouplingKernel_markov (μ : Measure α) [IsProbabilityMeasure μ]
    (k : Θ → α → ℝ≥0∞) (hk : Measurable (Function.uncurry k))
    (hnorm : ∀ s, (∫⁻ x, k s x ∂μ) = 1) :
    IsMarkovKernel (densityCouplingKernel μ k hk) := by
  constructor
  intro s
  exact densityCoupling_probability μ (k s) hk.of_uncurry_left (hnorm s)

theorem densityCouplingKernel_marginals (μ : Measure α) [IsProbabilityMeasure μ]
    (k : Θ → α → ℝ≥0∞) (hk : Measurable (Function.uncurry k))
    (hnorm : ∀ s, (∫⁻ x, k s x ∂μ) = 1) (s : Θ) :
    ((densityCouplingKernel μ k hk) s).map Prod.fst = μ.withDensity (k s) ∧
      ((densityCouplingKernel μ k hk) s).map Prod.snd = μ :=
  densityCoupling_marginals μ (k s) hk.of_uncurry_left (hnorm s)

#print axioms densityCoupling_measurable
#print axioms densityCouplingKernel_markov
end SpectralRadiusUpperTail
