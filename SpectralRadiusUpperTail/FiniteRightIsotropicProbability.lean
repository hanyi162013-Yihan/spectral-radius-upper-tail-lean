import SpectralRadiusUpperTail.FiniteRightIsotropicBound
import SpectralRadiusUpperTail.FiniteCorrectionBudget
import SpectralRadiusUpperTail.ScaledIsotropicBlock
import SpectralRadiusUpperTail.RectangularColumnEnergy

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator

/-- Isotropic approximation on a fixed exterior annulus. Test vectors are prescribed. -/
def matrixAnnulusIsotropicControl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (p q : Fin n → ℂ) (r L ε : ℝ) : Prop :=
  ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ L → z ∈ resolventSet ℂ A ∧
    ‖matrixCoefficient p q (resolvent A z)-z⁻¹*matrixCoefficient p q 1‖ < ε

lemma iid_finite_right_isotropic_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (m : ℕ) (hcard : ∀ n, Fintype.card (ι n) ≤ m)
    (P Q : (n : ℕ) → Matrix (Fin n) (ι n) ℂ) (C : ℝ) (hC : 0 < C)
    (hP : ∀ n, ‖P n‖ ≤ 1) (hQ : ∀ n, ‖Q n‖ ≤ C)
    (p q : (n : ℕ) → Fin n → ℂ)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1) (hq : ∀ n, (∑ i, ‖q n i‖^2) ≤ 1)
    (r L ε : ℝ) (hr : 1 < r) (hL : 0 < L) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixAnnulusIsotropicControl (normalizedIidMatrix x*(1+Q n*(P n)ᴴ))
        (p n) (q n) r L ε}) atTop (𝓝 0) := by
  obtain ⟨M,hM,hbase⟩ := iid_exterior_resolvent_probability μ c hc hexp hm hv r hr
  obtain ⟨δ,hδ,hbudget⟩ := exists_finite_correction_threshold m L M ε hL.le hM.le hε
  have hPe : ∀ n a, (∑ i, ‖P n i a‖^2) ≤ 1 := by
    intro n a
    simpa using rectangular_column_energy_le (P n) 1 (by norm_num) (hP n) a
  have hQe := fun n a => rectangular_column_energy_le (Q n) C hC.le (hQ n) a
  have hblock := iid_scaled_isotropic_block_probability μ c hc hexp hm hv ι m hcard P Q C hC
    hPe hQe r (1/(2*L)) hr (by positivity)
  have hleft := iid_scaled_isotropic_block_probability μ c hc hexp hm hv ι m hcard
    (fun n i _ => p n i) Q C hC (fun n _ => hp n) hQe r δ hr hδ
  have hiso := iid_isotropic_resolvent_probability μ c hc hexp hm hv p q hp hq r (ε/2) hr (by positivity)
  have ht := ((hbase.add hblock).add hleft).add hiso
  simp only [zero_add] at ht
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  apply (measureReal_mono (μ := Measure.pi (fun _ : Fin n × Fin n => μ)) ?_).trans
    ((measureReal_union_le _ _).trans (add_le_add
      ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) (le_refl _))) (le_refl _)))
  intro x hx
  by_contra hnot
  have hb : matrixExteriorControl (normalizedIidMatrix x) r M := by
    by_contra hh
    exact hnot (Or.inl (Or.inl (Or.inl hh)))
  have hi : matrixIsotropicBlockControl (normalizedIidMatrix x) (P n) (Q n) r (1/(2*L)) := by
    by_contra hh
    exact hnot (Or.inl (Or.inl (Or.inr hh)))
  have hl : matrixIsotropicBlockControl (normalizedIidMatrix x) (fun i _ => p n i) (Q n) r δ := by
    by_contra hh
    exact hnot (Or.inl (Or.inr hh))
  have hs : matrixIsotropicControl (normalizedIidMatrix x) (p n) (q n) r (ε/2) := by
    by_contra hh
    exact hnot (Or.inr hh)
  apply hx
  intro z hz hzL
  have hsmall0 := matrix_right_block_norm_le (normalizedIidMatrix x) (P n) (Q n)
    r L (1/(2*L)) (by linarith) (by positivity) hi z hz hzL
  have hcancel : L*(1/(2*L)) = (1:ℝ)/2 := by field_simp
  rw [hcancel] at hsmall0
  have hsmall : ‖(P n)ᴴ*resolvent (normalizedIidMatrix x) z*(normalizedIidMatrix x*Q n)‖ ≤ 1/2 := by
    simpa only [Matrix.mul_assoc] using hsmall0
  have hlc := fun j => right_column_coefficient_small (normalizedIidMatrix x) (p n) (Q n)
    r L δ (by linarith) hδ.le hl z hz hzL j
  have hf := finite_right_isotropic_error_bound (normalizedIidMatrix x) (P n) (Q n) (p n) (q n)
    (hPe n) (hq n) z (hb z hz).1 M (L*δ) hM.le (by positivity) (hb z hz).2 hsmall hlc
  refine ⟨hf.1,?_⟩
  have hrem := hbudget (Fintype.card (ι n)) (hcard n)
  have hmain := (hs z hz).2
  linarith [hf.2]

#print axioms matrixAnnulusIsotropicControl
#print axioms iid_finite_right_isotropic_probability
end SpectralRadiusUpperTail
