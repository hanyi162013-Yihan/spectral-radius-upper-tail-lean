import SpectralRadiusUpperTail.ScaledIsotropicBlock
import SpectralRadiusUpperTail.RectangularColumnEnergy
import SpectralRadiusUpperTail.MatrixRightBlockIdentity
import SpectralRadiusUpperTail.MatrixWoodburyNorm

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator

/-- Uniform resolvent norm control on a closed annulus, in Euclidean operator norm. -/
def matrixAnnulusControl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (r L B : ℝ) : Prop :=
  ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ L → z ∈ resolventSet ℂ A ∧
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (resolvent A z)‖ ≤ B

/-- The norm constant is independent of the finite family cardinality bound m. -/
lemma iid_finite_right_deformation_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (m : ℕ) (hcard : ∀ n, Fintype.card (ι n) ≤ m)
    (P Q : (n : ℕ) → Matrix (Fin n) (ι n) ℂ) (C : ℝ) (hC : 0 < C)
    (hP : ∀ n, ‖P n‖ ≤ 1) (hQ : ∀ n, ‖Q n‖ ≤ C)
    (r L M : ℝ) (hr : 1 < r) (hL : 0 < L) (hM : 0 < M)
    (hbase : Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixExteriorControl (normalizedIidMatrix x) r M}) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixAnnulusControl (normalizedIidMatrix x*(1+Q n*(P n)ᴴ)) r L
        (M+6*M^2*C)}) atTop (𝓝 0) := by
  have hPe : ∀ n a, (∑ i, ‖P n i a‖^2) ≤ 1 := by
    intro n a
    simpa using rectangular_column_energy_le (P n) 1 (by norm_num) (hP n) a
  have hQe := fun n a => rectangular_column_energy_le (Q n) C hC.le (hQ n) a
  have hblock := iid_scaled_isotropic_block_probability μ c hc hexp hm hv ι m hcard P Q C hC
    hPe hQe r (1/(2*L)) hr (by positivity)
  have hpower := normalizedPower_operator_probability_tendsto μ c hc hexp hm hv 1 3 (by norm_num)
  simp only [pow_one] at hpower
  have ht := (hbase.add hpower).add hblock
  simp only [zero_add] at ht
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  apply (measureReal_mono (μ := Measure.pi (fun _ : Fin n × Fin n => μ)) ?_).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) (le_refl _)))
  intro x hx
  by_contra hnot
  have hb : matrixExteriorControl (normalizedIidMatrix x) r M := by
    by_contra hh
    exact hnot (Or.inl (Or.inl hh))
  have hy : ‖normalizedIidMatrix x‖ ≤ 3 := by
    by_contra hh
    exact hnot (Or.inl (Or.inr (le_of_lt (lt_of_not_ge hh))))
  have hi : matrixIsotropicBlockControl (normalizedIidMatrix x) (P n) (Q n) r (1/(2*L)) := by
    by_contra hh
    exact hnot (Or.inr hh)
  apply hx
  intro z hz hzL
  have hs := matrix_right_block_norm_le (normalizedIidMatrix x) (P n) (Q n)
    r L (1/(2*L)) (by linarith) (by positivity) hi z hz hzL
  have hcancel : L*(1/(2*L)) = (1:ℝ)/2 := by field_simp
  rw [hcancel] at hs
  have hsmall : ‖(P n)ᴴ*resolvent (normalizedIidMatrix x) z*(normalizedIidMatrix x*Q n)‖ ≤ 1/2 := by
    simpa only [Matrix.mul_assoc] using hs
  have hU : ‖normalizedIidMatrix x*Q n‖ ≤ 3*C := (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul hy (hQ n) (norm_nonneg _) (by norm_num))
  have hV : ‖(P n)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hP n
  have hw := matrix_woodbury_norm_bound (normalizedIidMatrix x) (normalizedIidMatrix x*Q n)
    (P n)ᴴ z (hb z hz).1 M (3*C) 1 hM.le (by positivity) (by norm_num) (hb z hz).2 hU hV hsmall
  have he : normalizedIidMatrix x*(1+Q n*(P n)ᴴ) =
      normalizedIidMatrix x+(normalizedIidMatrix x*Q n)*(P n)ᴴ := by
    rw [Matrix.mul_add,Matrix.mul_one,Matrix.mul_assoc]
  rw [he]
  refine ⟨hw.1,hw.2.trans_eq ?_⟩
  ring

#print axioms matrixAnnulusControl
#print axioms iid_finite_right_deformation_probability
end SpectralRadiusUpperTail
