import SpectralRadiusUpperTail.IidIsotropicBlock
import SpectralRadiusUpperTail.MatrixColumnNormalization

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma isotropic_block_scale_right (A : Matrix (Fin n) (Fin n) ℂ)
    (P Q : Matrix (Fin n) ι ℂ) (C r ε : ℝ) (hC : 0 < C)
    (h : matrixIsotropicBlockControl A P ((C : ℂ)⁻¹ • Q) r (ε/C)) :
    matrixIsotropicBlockControl A P Q r ε := by
  intro z hz
  refine ⟨(h z hz).1,?_⟩
  have he : Pᴴ*resolvent A z*Q-z⁻¹ • (Pᴴ*Q) =
      (C : ℂ) • (Pᴴ*resolvent A z*((C : ℂ)⁻¹ • Q)-
        z⁻¹ • (Pᴴ*((C : ℂ)⁻¹ • Q))) := by
    have hc : (C : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hC
    simp only [Matrix.mul_smul,smul_sub,smul_smul]
    rw [mul_inv_cancel₀ hc,one_smul]
    have hs : (C : ℂ)*(z⁻¹*(C : ℂ)⁻¹) = z⁻¹ := by field_simp
    rw [hs]
  change ‖Pᴴ*resolvent A z*Q-z⁻¹ • (Pᴴ*Q)‖ < ε
  rw [he,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hC]
  have hh := mul_lt_mul_of_pos_left (h z hz).2 hC
  have hcancel : C*(ε/C) = ε := by field_simp
  exact hh.trans_eq hcancel

lemma iid_scaled_isotropic_block_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (m : ℕ) (hcard : ∀ n, Fintype.card (ι n) ≤ m)
    (P Q : (n : ℕ) → Matrix (Fin n) (ι n) ℂ) (C : ℝ) (hC : 0 < C)
    (hP : ∀ n a, (∑ i, ‖P n i a‖^2) ≤ 1)
    (hQ : ∀ n a, (∑ i, ‖Q n i a‖^2) ≤ C^2)
    (r ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixIsotropicBlockControl (normalizedIidMatrix x) (P n) (Q n) r ε})
      atTop (𝓝 0) := by
  have ht := iid_isotropic_block_probability μ c hc hexp hm hv ι m hcard P
    (fun n => (C : ℂ)⁻¹ • Q n) hP
    (fun n => matrix_inv_scale_column_energy (Q n) C hC (hQ n)) r (ε/C) hr (div_pos hε hC)
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  apply measureReal_mono (μ := Measure.pi (fun _ : Fin n × Fin n => μ))
  intro x hx hs
  exact hx (isotropic_block_scale_right (normalizedIidMatrix x) (P n) (Q n) C r ε hC hs)

#print axioms isotropic_block_scale_right
#print axioms iid_scaled_isotropic_block_probability
end SpectralRadiusUpperTail
