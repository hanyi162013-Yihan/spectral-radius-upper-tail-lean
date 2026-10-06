import SpectralRadiusUpperTail.BoundedIsotropicFamily
import SpectralRadiusUpperTail.IsotropicBlockControl

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators Matrix

lemma iid_isotropic_block_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (m : ℕ) (hcard : ∀ n, Fintype.card (ι n) ≤ m)
    (P Q : (n : ℕ) → Matrix (Fin n) (ι n) ℂ)
    (hP : ∀ n a, (∑ i, ‖P n i a‖^2) ≤ 1)
    (hQ : ∀ n a, (∑ i, ‖Q n i a‖^2) ≤ 1)
    (r ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixIsotropicBlockControl (normalizedIidMatrix x) (P n) (Q n) r ε})
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbase⟩ := iid_exterior_resolvent_probability μ c hc hexp hm hv r hr
  let δ := ε/(2*(m+1 : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hprod : ∀ n, Fintype.card (ι n × ι n) ≤ m*m := by
    intro n
    rw [Fintype.card_prod]
    exact Nat.mul_le_mul (hcard n) (hcard n)
  have hentries := iid_bounded_isotropic_probability μ c hc hexp hm hv
    (fun n => ι n × ι n) (m*m) hprod
    (fun n a i => P n i a.1) (fun n a i => Q n i a.2)
    (fun n a => hP n a.1) (fun n a => hQ n a.2) r δ hr hδ
  have ht := hbase.add hentries
  simp only [zero_add] at ht
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  apply (measureReal_mono (μ := Measure.pi (fun _ : Fin n × Fin n => μ)) ?_).trans
    (measureReal_union_le _ _)
  intro x hx
  by_contra hnot
  have hb : matrixExteriorControl (normalizedIidMatrix x) r C := by
    by_contra hh
    exact hnot (Or.inl hh)
  have he : ∀ i j, matrixIsotropicControl (normalizedIidMatrix x)
      (fun k => P n k i) (fun k => Q n k j) r δ := by
    intro i j
    by_contra hh
    exact hnot (Or.inr ⟨(i,j),hh⟩)
  have hs : (Fintype.card (ι n) : ℝ)*δ < ε := by
    have hm' : (Fintype.card (ι n) : ℝ) ≤ m := by exact_mod_cast hcard n
    have hd : (m : ℝ)*δ < ε := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (by positivity : (0:ℝ) < 2*(m+1 : ℝ))).mpr
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    exact (mul_le_mul_of_nonneg_right hm' hδ.le).trans_lt hd
  exact hx (isotropic_block_of_entries (normalizedIidMatrix x) (P n) (Q n) r ε δ hδ.le hs
    (fun z hz => (hb z hz).1) he)

#print axioms iid_isotropic_block_probability
end SpectralRadiusUpperTail
