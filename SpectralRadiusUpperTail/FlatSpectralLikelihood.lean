import SpectralRadiusUpperTail.FlatSpectralMatrixWeight
import SpectralRadiusUpperTail.ChangeMeasureLogLower

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped ENNReal Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {n : ℕ} {L : ℝ}

noncomputable def flatSpectralMatrixLikelihood (μ : Measure 𝕂)
    (ν : Measure (flatUnitDirections 𝕂 n L)) (a : ℝ) (b : 𝕂)
    (x : Fin n → Fin n → 𝕂) : ℝ≥0∞ :=
  flatSpectralMatrixWeight ν a b x /
    ∫⁻ y, flatSpectralMatrixWeight ν a b y
      ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))

lemma flatSpectralMatrixLikelihood_measurable (μ : Measure 𝕂)
    (ν : Measure (flatUnitDirections 𝕂 n L)) [SFinite ν] (a : ℝ) (b : 𝕂) :
    Measurable (flatSpectralMatrixLikelihood μ ν a b) :=
  (flatSpectralMatrixWeight_measurable ν a b).div_const _

lemma flatSpectralMatrixTilt_density (μ : Measure 𝕂)
    (ν : Measure (flatUnitDirections 𝕂 n L)) (a : ℝ) (b : 𝕂) :
    flatSpectralMatrixTilt μ ν a b =
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).withDensity
        (flatSpectralMatrixLikelihood μ ν a b) := rfl

lemma flatSpectralMatrixTilt_log_lower_from_cost
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (a : ℝ) (ha : 0 < a) (L : ℝ)
    (ν : (n : ℕ) → Measure (flatUnitDirections 𝕂 n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : 𝕂) (A : (n : ℕ) → Set (Fin n → Fin n → 𝕂))
    (hA : ∀ n, MeasurableSet (A n))
    (hgood : Tendsto (fun n => (flatSpectralMatrixTilt μ (ν n) a b).real ((A n)ᶜ)) atTop (𝓝 0))
    (C : ℝ)
    (hcost : Tendsto (fun n => (flatSpectralMatrixTilt μ (ν n) a b).real
      {x | ENNReal.ofReal (Real.exp ((n : ℝ)*C)) < flatSpectralMatrixLikelihood μ (ν n) a b x})
      atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, -C-ε ≤
      Real.log ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real (A n))/(n : ℝ) := by
  let M := fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))
  let f := fun n => flatSpectralMatrixLikelihood μ (ν n) a b
  have (n : ℕ) : IsProbabilityMeasure ((M n).withDensity (f n)) :=
    flatSpectralMatrixTilt_probability μ (ν n) a ha b
  apply change_measure_eventual_log_lower (fun n => Fin n → Fin n → 𝕂) M f A
    (fun n => {x | f n x ≤ ENNReal.ofReal (Real.exp ((n : ℝ)*C))}) hA
  · intro n
    exact measurableSet_le (flatSpectralMatrixLikelihood_measurable μ (ν n) a b) measurable_const
  · exact hgood
  · simpa only [Set.compl_setOf,not_le,M,f,← flatSpectralMatrixTilt_density] using hcost
  · exact Eventually.of_forall (fun n x hx => hx)
  · exact hε

#print axioms flatSpectralMatrixLikelihood
#print axioms flatSpectralMatrixLikelihood_measurable
#print axioms flatSpectralMatrixTilt_density
#print axioms flatSpectralMatrixTilt_log_lower_from_cost
end SpectralRadiusUpperTail
