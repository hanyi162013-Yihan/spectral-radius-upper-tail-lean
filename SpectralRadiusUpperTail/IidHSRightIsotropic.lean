import SpectralRadiusUpperTail.AnnulusIsotropicPerturbation
import SpectralRadiusUpperTail.IidHSRightDeformation
import SpectralRadiusUpperTail.ResolventTruncationBudget

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator

lemma iid_HS_right_isotropic_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (C : ℝ) (hC : 0 < C)
    (hD : ∀ n, matrixHSsq (D n) ≤ C^2)
    (p q : (n : ℕ) → Fin n → ℂ)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1) (hq : ∀ n, (∑ i, ‖q n i‖^2) ≤ 1)
    (r L ε : ℝ) (hr : 1 < r) (hL : 0 < L) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixAnnulusIsotropicControl (normalizedIidMatrix x*(1+D n))
        (p n) (q n) r L ε}) atTop (𝓝 0) := by
  classical
  obtain ⟨M,hM,hbase⟩ := iid_exterior_resolvent_probability μ c hc hexp hm hv r hr
  let B := M+6*M^2*C
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨δ,hδ,hsmallδ,herrorδ⟩ := exists_resolvent_truncation_threshold B ε hB hε
  choose s W hgram hW hDW herr hcard using
    (fun n => matrix_HS_frame_truncation (D n) C δ hC.le (hD n) hδ.le)
  let m := ⌈C^2/δ^2⌉₊
  have hsize : ∀ n, Fintype.card (s n) ≤ m := by
    intro n
    rw [Fintype.card_coe]
    exact truncation_card_bound (s n) C δ hδ (hcard n)
  have hfinite := iid_finite_right_deformation_probability μ c hc hexp hm hv
    (fun n => s n) m hsize W (fun n => D n*W n) C hC hW hDW r L M hr hL hM hbase
  have hiso := iid_finite_right_isotropic_probability μ c hc hexp hm hv
    (fun n => s n) m hsize W (fun n => D n*W n) C hC hW hDW p q hp hq r L (ε/2) hr hL (by positivity)
  have hpower := normalizedPower_operator_probability_tendsto μ c hc hexp hm hv 1 3 (by norm_num)
  simp only [pow_one] at hpower
  have ht := (hfinite.add hiso).add hpower
  simp only [zero_add] at ht
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  apply (measureReal_mono (μ := Measure.pi (fun _ : Fin n × Fin n => μ)) ?_).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) (le_refl _)))
  intro x hx
  by_contra hnot
  have hb : matrixAnnulusControl (normalizedIidMatrix x*(1+(D n*W n)*(W n)ᴴ)) r L B := by
    by_contra hh
    exact hnot (Or.inl (Or.inl hh))
  have hi : matrixAnnulusIsotropicControl (normalizedIidMatrix x*(1+(D n*W n)*(W n)ᴴ))
      (p n) (q n) r L (ε/2) := by
    by_contra hh
    exact hnot (Or.inl (Or.inr hh))
  have hy : ‖normalizedIidMatrix x‖ ≤ 3 := by
    by_contra hh
    exact hnot (Or.inr (le_of_lt (lt_of_not_ge hh)))
  let E := normalizedIidMatrix x*(D n-D n*W n*(W n)ᴴ)
  have he : ‖E‖ ≤ 3*δ := (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul hy (herr n) (norm_nonneg _) (by norm_num))
  have hs : B*‖E‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left he hB.le).trans hsmallδ
  have hd : 2*B^2*‖E‖ ≤ ε/4 :=
    (mul_le_mul_of_nonneg_left he (by positivity)).trans herrorδ
  have hid : normalizedIidMatrix x*(1+D n) =
      normalizedIidMatrix x*(1+(D n*W n)*(W n)ᴴ)+E := by
    dsimp [E]
    rw [← Matrix.mul_add]
    congr 1
    abel
  apply hx
  rw [hid]
  exact annulus_isotropic_add _ E (p n) (q n) (hp n) (hq n) r L B ε hB.le hε hb hi hs hd

#print axioms iid_HS_right_isotropic_probability
end SpectralRadiusUpperTail
