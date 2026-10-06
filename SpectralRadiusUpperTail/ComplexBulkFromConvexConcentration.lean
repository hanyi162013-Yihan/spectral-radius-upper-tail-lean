import SpectralRadiusUpperTail.RegularizedConvexObservables
import SpectralRadiusUpperTail.LipschitzArrayIntegrable
import SpectralRadiusUpperTail.ConcentrationDifference
import SpectralRadiusUpperTail.ConcentrationMap

namespace SpectralRadiusUpperTail
open MeasureTheory Filter WithLp
open scoped Topology NNReal

/-- The matrix-specific centered bulk estimate follows from the usual uniform
product-space concentration theorem for convex Lipschitz observables. -/
lemma complex_bulk_concentration_of_convex_concentration
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : Integrable (fun x : ℂ => ‖x‖^2) μ)
    (hconv : ∀ (L : ℝ≥0) (δ : ℝ), 0 < (L : ℝ) → 0 < δ →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        ∀ f : EuclideanSpace ℂ (Fin (n*n)) → ℝ,
          ConvexOn ℝ Set.univ f → LipschitzWith (L/(n : ℝ≥0)) f →
          (Measure.pi (fun _ : Fin (n*n) => μ)).real
            {x | δ < |f (toLp 2 x)-(∫ y : Fin (n*n) → ℂ, f (toLp 2 y)
              ∂Measure.pi (fun _ => μ))|} ≤ C*Real.exp (-q*(n : ℝ)^2))
    (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ z : ℂ,
        (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
          {x | δ < |regularizedResidualLogDet x z s/(n : ℝ)-
            ∫ y : Fin n → Fin n → ℂ, regularizedResidualLogDet y z s/(n : ℝ)
              ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))|} ≤ C*Real.exp (-q*(n : ℝ)^2) := by
  let τ := Real.sqrt s
  have hτ : 0 < τ := Real.sqrt_pos.mpr hs
  have hτs : τ^2 = s := Real.sq_sqrt hs.le
  let L := Real.toNNReal (1/τ)
  have hL : 0 < (L : ℝ) := by
    change 0 < (Real.toNNReal (1/τ) : ℝ)
    rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 1/τ)]
    positivity
  obtain ⟨C, hC, q, hq, ht⟩ := hconv L (δ/2) hL (by positivity)
  refine ⟨2*C, by positivity, q, hq, ?_⟩
  filter_upwards [ht, eventually_gt_atTop 0] with n hn hn0 z
  let F := normalizedSingularObservable n z (regularizedLogConvex₁ τ)
  let G := normalizedSingularObservable n z (regularizedLogConvex₂ τ)
  have hF := regularized_convex_observable₁ n hn0 z τ hτ
  have hG := regularized_convex_observable₂ n hn0 z τ hτ
  let T : (Fin (n*n) → ℂ) → ℝ := fun x => 2*Real.log τ+F (toLp 2 x)-G (toLp 2 x)
  have hFi := lipschitz_iid_array_integrable μ (n*n) h2 (L/(n : ℝ≥0)) F hF.2
  have hGi := lipschitz_iid_array_integrable μ (n*n) h2 (L/(n : ℝ≥0)) G hG.2
  have hbound := centered_difference_tail (Measure.pi (fun _ : Fin (n*n) => μ))
    (fun x => F (toLp 2 x)) (fun x => G (toLp 2 x)) hFi hGi (2*Real.log τ) δ
  have hFb := hn F hF.1 hF.2
  have hGb := hn G hG.1 hG.2
  have hTbound : (Measure.pi (fun _ : Fin (n*n) => μ)).real
      {x | δ < |T x-(∫ y, T y ∂Measure.pi (fun _ : Fin (n*n) => μ))|} ≤
        (2*C)*Real.exp (-q*(n : ℝ)^2) := by
    change _ ≤ _ at hbound
    calc
      _ ≤ _ := hbound
      _ ≤ C*Real.exp (-q*(n : ℝ)^2)+C*Real.exp (-q*(n : ℝ)^2) := add_le_add hFb hGb
      _ = _ := by ring
  letI : MeasurableSpace (EuclideanSpace ℂ (Fin (n*n))) := borel _
  letI : BorelSpace (EuclideanSpace ℂ (Fin (n*n))) := ⟨rfl⟩
  have hmlp : Measurable (fun x : Fin (n*n) → ℂ => toLp 2 x) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin (n*n) => ℂ)).measurable
  have hTm : Measurable T :=
    (measurable_const.add (hF.2.continuous.measurable.comp hmlp)).sub
      (hG.2.continuous.measurable.comp hmlp)
  have he := centered_tail_map
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
    (Measure.pi (fun _ : Fin (n*n) => μ)) serialMatrixEntries
    (serialMatrixEntries_measurable n) (iid_serial_matrix_law μ n) T hTm δ
  have hid (x : Fin n → Fin n → ℂ) : regularizedResidualLogDet x z s/(n : ℝ) = T (serialMatrixEntries x) := by
    rw [← hτs]
    exact regularizedResidualLogDet_convex_decomposition n hn0 z τ hτ x
  simpa only [hid] using! he.trans_le hTbound

#print axioms complex_bulk_concentration_of_convex_concentration
end SpectralRadiusUpperTail
