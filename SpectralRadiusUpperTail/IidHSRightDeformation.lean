import SpectralRadiusUpperTail.FiniteRightDeformationProbability
import SpectralRadiusUpperTail.MatrixHSFrameTruncation
import SpectralRadiusUpperTail.ResolventQuantitative

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator

/-- Actual iid right deformations with a uniform Hilbert--Schmidt budget have
uniform exterior-annulus resolvent norm bounds with probability tending to one. -/
lemma iid_HS_right_annulus_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (C : ℝ) (hC : 0 < C)
    (hD : ∀ n, matrixHSsq (D n) ≤ C^2)
    (r L : ℝ) (hr : 1 < r) (hL : 0 < L) :
    ∃ B : ℝ, 0 < B ∧ Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixAnnulusControl (normalizedIidMatrix x*(1+D n)) r L B}) atTop (𝓝 0) := by
  classical
  obtain ⟨M,hM,hbase⟩ := iid_exterior_resolvent_probability μ c hc hexp hm hv r hr
  let B := M+6*M^2*C
  have hB : 0 < B := by dsimp [B]; positivity
  let δ := 1/(6*B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  choose s W hgram hW hDW herr hcard using
    (fun n => matrix_HS_frame_truncation (D n) C δ hC.le (hD n) hδ.le)
  let m := ⌈C^2/δ^2⌉₊
  have hsize : ∀ n, Fintype.card (s n) ≤ m := by
    intro n
    rw [Fintype.card_coe]
    exact truncation_card_bound (s n) C δ hδ (hcard n)
  have hfinite := iid_finite_right_deformation_probability μ c hc hexp hm hv
    (fun n => s n) m hsize W (fun n => D n*W n) C hC hW hDW r L M hr hL hM hbase
  have hpower := normalizedPower_operator_probability_tendsto μ c hc hexp hm hv 1 3 (by norm_num)
  simp only [pow_one] at hpower
  have ht := hfinite.add hpower
  simp only [zero_add] at ht
  refine ⟨2*B,by positivity,?_⟩
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  apply (measureReal_mono (μ := Measure.pi (fun _ : Fin n × Fin n => μ)) ?_).trans
    (measureReal_union_le _ _)
  intro x hx
  by_contra hnot
  have hb : matrixAnnulusControl (normalizedIidMatrix x*(1+(D n*W n)*(W n)ᴴ)) r L B := by
    by_contra hh
    exact hnot (Or.inl hh)
  have hy : ‖normalizedIidMatrix x‖ ≤ 3 := by
    by_contra hh
    exact hnot (Or.inr (le_of_lt (lt_of_not_ge hh)))
  let E := normalizedIidMatrix x*(D n-D n*W n*(W n)ᴴ)
  have he : ‖E‖ ≤ 3*δ := (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul hy (herr n) (norm_nonneg _) (by norm_num))
  have hs : B*‖E‖ ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left he hB.le
    have hcanc : B*(3*δ) = (1:ℝ)/2 := by dsimp [δ]; field_simp <;> norm_num
    exact hh.trans_eq hcanc
  have hid : normalizedIidMatrix x*(1+D n) =
      normalizedIidMatrix x*(1+(D n*W n)*(W n)ᴴ)+E := by
    dsimp [E]
    rw [← Matrix.mul_add]
    congr 1
    abel
  apply hx
  intro z hz hzL
  have hh := resolvent_add_quantitative
    (normalizedIidMatrix x*(1+(D n*W n)*(W n)ᴴ)) E z B hB.le
    (hb z hz hzL).1 (hb z hz hzL).2 hs
  rw [hid]
  exact ⟨hh.1,hh.2.1⟩

#print axioms iid_HS_right_annulus_probability
end SpectralRadiusUpperTail
