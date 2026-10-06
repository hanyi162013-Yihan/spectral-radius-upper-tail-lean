import SpectralRadiusUpperTail.ConvexSetMedianTail
import SpectralRadiusUpperTail.ProbabilityMedianExists
import SpectralRadiusUpperTail.MedianConcentrationTransfer

namespace SpectralRadiusUpperTail
open MeasureTheory Filter WithLp
open scoped Topology NNReal
variable {𝕂 : Type*} [RCLike 𝕂]

/-- Dimension-free convex-set separation for each fixed bounded entry law.
This is an explicit remaining probabilistic input, not an asserted theorem. -/
def CutoffConvexSeparation (μ : Measure 𝕂) : Prop :=
  ∀ K : ℕ, ∃ q : ℝ, 0 < q ∧ ∀ N : ℕ,
    ConvexSetSeparation (Measure.pi (fun _ : Fin N => μ.map (entryCutoff (K : ℝ))))
      (fun x : Fin N → 𝕂 => toLp 2 x) q

lemma cutoff_median_concentration_of_separation (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hsep : CutoffConvexSeparation μ) : CutoffMedianConcentration μ := by
  intro K L δ hL hδ
  letI : IsProbabilityMeasure (μ.map (entryCutoff (K : ℝ))) :=
    Measure.isProbabilityMeasure_map (entryCutoff_measurable (K : ℝ)).aemeasurable
  obtain ⟨q, hq, hgeom⟩ := hsep K
  refine ⟨4, by norm_num, q*(δ/(L : ℝ))^2, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn f hfc hf
  letI : MeasurableSpace (EuclideanSpace 𝕂 (Fin (n*n))) := borel _
  letI : BorelSpace (EuclideanSpace 𝕂 (Fin (n*n))) := ⟨rfl⟩
  have hm : Measurable (fun x : Fin (n*n) → 𝕂 => f (toLp 2 x)) :=
    hf.continuous.measurable.comp (PiLp.continuous_toLp 2 (fun _ : Fin (n*n) => 𝕂)).measurable
  obtain ⟨m, hmed⟩ := probability_median_exists
    (Measure.pi (fun _ : Fin (n*n) => μ.map (entryCutoff (K : ℝ)))) _ hm
  refine ⟨m, hmed, ?_⟩
  have hCn : 0 < ((L/(n : ℝ≥0) : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_div, NNReal.coe_natCast]
    exact div_pos hL (Nat.cast_pos.mpr hn)
  have ht := convex_median_tail_of_separation _ (fun x : Fin (n*n) → 𝕂 => toLp 2 x)
    q (hgeom (n*n)) (L/(n : ℝ≥0)) hCn f hfc hf m δ hδ hmed
  convert! ht using 1
  simp only [NNReal.coe_div, NNReal.coe_natCast]
  congr 2
  field_simp
  <;> ring

lemma cutoff_concentration_of_separation (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hsep : CutoffConvexSeparation μ) : CutoffConvexConcentration μ :=
  cutoff_concentration_of_median μ (cutoff_median_concentration_of_separation μ hsep)

#print axioms cutoff_median_concentration_of_separation
#print axioms cutoff_concentration_of_separation
end SpectralRadiusUpperTail
