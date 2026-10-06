import SpectralRadiusUpperTail.UnboundedConcentrationReduction
import SpectralRadiusUpperTail.LipschitzCutoffIntegrable
import SpectralRadiusUpperTail.ConcentrationMap
import SpectralRadiusUpperTail.ConcentrationDifference

namespace SpectralRadiusUpperTail
open MeasureTheory Filter WithLp
open scoped Topology NNReal
variable {𝕂 : Type*} [RCLike 𝕂]

/-- Once convex concentration is available for each fixed bounded cutoff law,
square-exponential truncation transfers it to the original iid law. -/
lemma convex_concentration_of_cutoff_laws (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : 𝕂 => Real.exp (c*‖x‖^2)) μ)
    (h2 : Integrable (fun x : 𝕂 => ‖x‖^2) μ)
    (hcut : ∀ (K : ℕ) (L : ℝ≥0) (δ : ℝ), 0 < (L : ℝ) → 0 < δ →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        ∀ f : EuclideanSpace 𝕂 (Fin (n*n)) → ℝ,
          ConvexOn ℝ Set.univ f → LipschitzWith (L/(n : ℝ≥0)) f →
          (Measure.pi (fun _ : Fin (n*n) => μ.map (entryCutoff (K : ℝ)))).real
            {x | δ < |f (toLp 2 x)-(∫ y : Fin (n*n) → 𝕂, f (toLp 2 y)
              ∂Measure.pi (fun _ => μ.map (entryCutoff (K : ℝ))))|} ≤ C*Real.exp (-q*(n : ℝ)^2))
    (L : ℝ≥0) (δ : ℝ) (hL : 0 < (L : ℝ)) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ f : EuclideanSpace 𝕂 (Fin (n*n)) → ℝ,
        ConvexOn ℝ Set.univ f → LipschitzWith (L/(n : ℝ≥0)) f →
        (Measure.pi (fun _ : Fin (n*n) => μ)).real
          {x | δ < |f (toLp 2 x)-(∫ y : Fin (n*n) → 𝕂, f (toLp 2 y)
            ∂Measure.pi (fun _ => μ))|} ≤ C*Real.exp (-q*(n : ℝ)^2) := by
  obtain ⟨K, q, hq, hred⟩ := unbounded_concentration_reduction μ c δ L hc hδ hL hexp h2
  obtain ⟨C, hC, p, hp, hbounded⟩ := hcut K L (δ/2) hL (by positivity)
  refine ⟨C+1, by positivity, min p q, lt_min hp hq, ?_⟩
  filter_upwards [hbounded, eventually_gt_atTop 0] with n hn hn0 f hfc hf
  have hFi := lipschitz_iid_array_integrable μ (n*n) h2 _ f hf
  have hGi := lipschitz_iid_cutoff_integrable μ n hn0 (K : ℝ) L h2 f hf
  have hr := hred n hn0 f hf hFi hGi
  dsimp only at hr
  letI : MeasurableSpace (EuclideanSpace 𝕂 (Fin (n*n))) := borel _
  letI : BorelSpace (EuclideanSpace 𝕂 (Fin (n*n))) := ⟨rfl⟩
  have hmlp : Measurable (fun x : Fin (n*n) → 𝕂 => toLp 2 x) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin (n*n) => 𝕂)).measurable
  have hmcut : Measurable (fun x : Fin (n*n) → 𝕂 => fun i => entryCutoff (K : ℝ) (x i)) :=
    measurable_pi_lambda _ (fun i => (entryCutoff_measurable (K : ℝ)).comp (measurable_pi_apply i))
  have he := centered_tail_map (Measure.pi (fun _ : Fin (n*n) => μ))
    (Measure.pi (fun _ : Fin (n*n) => μ.map (entryCutoff (K : ℝ))))
    (fun x : Fin (n*n) → 𝕂 => fun i => entryCutoff (K : ℝ) (x i)) hmcut
    (entryCutoff_product_law μ (n*n) (K : ℝ))
    (fun x => f (toLp 2 x)) (hf.continuous.measurable.comp hmlp) (δ/2)
  rw [he] at hr
  apply hr.trans
  apply (add_le_add (hn f hfc hf) (le_refl (Real.exp (-q*(n : ℝ)^2)))).trans
  simpa only [one_mul] using sum_quadratic_exponential_bounds C 1 p q n hC (by norm_num)

#print axioms convex_concentration_of_cutoff_laws
end SpectralRadiusUpperTail
