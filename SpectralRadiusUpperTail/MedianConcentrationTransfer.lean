import SpectralRadiusUpperTail.BoundedMedianRange
import SpectralRadiusUpperTail.BoundedArrayObservableRange
import SpectralRadiusUpperTail.QuadraticExponentialVanish
import SpectralRadiusUpperTail.ConvexConcentrationInput

namespace SpectralRadiusUpperTail
open MeasureTheory Filter WithLp
open scoped Topology NNReal
variable {𝕂 : Type*} [RCLike 𝕂]

/-- Median form of the remaining bounded-product concentration input. The
center is a genuine probability median, not a new free mean hypothesis. -/
def CutoffMedianConcentration (μ : Measure 𝕂) : Prop :=
  ∀ (K : ℕ) (L : ℝ≥0) (δ : ℝ), 0 < (L : ℝ) → 0 < δ →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ f : EuclideanSpace 𝕂 (Fin (n*n)) → ℝ,
        ConvexOn ℝ Set.univ f → LipschitzWith (L/(n : ℝ≥0)) f →
        ∃ m : ℝ,
          IsProbabilityMedian (Measure.pi (fun _ : Fin (n*n) => μ.map (entryCutoff (K : ℝ))))
            (fun x => f (toLp 2 x)) m ∧
          (Measure.pi (fun _ : Fin (n*n) => μ.map (entryCutoff (K : ℝ)))).real
            {x | δ < |f (toLp 2 x)-m|} ≤ C*Real.exp (-q*(n : ℝ)^2)

lemma cutoff_square_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ] (K : ℕ) :
    Integrable (fun z : 𝕂 => ‖z‖^2) (μ.map (entryCutoff (K : ℝ)))  := by
  letI : IsProbabilityMeasure (μ.map (entryCutoff (K : ℝ))) :=
    Measure.isProbabilityMeasure_map (entryCutoff_measurable (K : ℝ)).aemeasurable
  apply (integrable_const ((K : ℝ)^2)).mono' (by fun_prop)
  filter_upwards [entryCutoff_law_supported μ (K : ℝ) (by positivity)] with z hz
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖z‖)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hz

/-- Uniform quadratic-speed concentration about medians gives the precise
centered concentration used in the log-det proof, for real or complex entries. -/
lemma cutoff_concentration_of_median (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hmed : CutoffMedianConcentration μ) : CutoffConvexConcentration μ := by
  intro K L δ hL hδ
  letI : IsProbabilityMeasure (μ.map (entryCutoff (K : ℝ))) :=
    Measure.isProbabilityMeasure_map (entryCutoff_measurable (K : ℝ)).aemeasurable
  obtain ⟨C, hC, q, hq, ht⟩ := hmed K L (δ/4) hL (by positivity)
  refine ⟨C, hC, q, hq, ?_⟩
  filter_upwards [ht, eventually_gt_atTop 0,
    eventually_quadratic_exponential_le (2*(L : ℝ)*(K : ℝ)*C) q (δ/4)
      (by positivity) hq (by positivity)] with n hn hn0 hsmall f hfc hf
  obtain ⟨m, hm, hb⟩ := hn f hfc hf
  let ν := Measure.pi (fun _ : Fin (n*n) => μ.map (entryCutoff (K : ℝ)))
  let F := fun x : Fin (n*n) → 𝕂 => f (toLp 2 x)
  letI : MeasurableSpace (EuclideanSpace 𝕂 (Fin (n*n))) := borel _
  letI : BorelSpace (EuclideanSpace 𝕂 (Fin (n*n))) := ⟨rfl⟩
  have hF : Measurable F :=
    hf.continuous.measurable.comp (PiLp.continuous_toLp 2 (fun _ : Fin (n*n) => 𝕂)).measurable
  have hi : Integrable F ν := lipschitz_iid_array_integrable
    (μ.map (entryCutoff (K : ℝ))) (n*n) (cutoff_square_integrable μ K) _ f hf
  have hbound : ∀ᵐ x ∂ν, |F x-m| ≤ 2*((L : ℝ)*(K : ℝ)) :=
    bounded_distance_to_median ν F m (f 0) ((L : ℝ)*(K : ℝ)) hm
      (cutoff_product_observable_range μ n hn0 K L f hf)
  have hmean : |(∫ x, F x ∂ν)-m| ≤ δ/2 := by
    have he := bounded_mean_distance_of_tail ν F hF hi m (2*((L : ℝ)*(K : ℝ)))
      (δ/4) (by positivity) hbound
    have hb' := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2*((L : ℝ)*(K : ℝ)))
    have hs : 2*((L : ℝ)*(K : ℝ))*(C*Real.exp (-q*(n : ℝ)^2)) ≤ δ/4 := by
      convert! hsmall using 1 <;> ring
    linarith
  apply (centered_tail_le_center_tail ν F m δ hmean).trans
  apply le_trans (measureReal_mono (μ := ν) ?_ (measure_ne_top _ _)) hb
  intro x hx
  change δ/2 < |F x-m| at hx
  change δ/4 < |F x-m|
  linarith

#print axioms cutoff_square_integrable
#print axioms cutoff_concentration_of_median
end SpectralRadiusUpperTail
