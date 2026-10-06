import SpectralRadiusUpperTail.RealSchurBlockNorm
import SpectralRadiusUpperTail.SchurGapLaw

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix Matrix.Norms.Frobenius

noncomputable def schurGapUpper (y s : ℝ) : ℝ :=
  (Real.sqrt (max 0 s+4*y^2)+Real.sqrt (max 0 s))/2
noncomputable def schurGapLower (y s : ℝ) : ℝ :=
  (Real.sqrt (max 0 s+4*y^2)-Real.sqrt (max 0 s))/2

lemma schurGapBlock_product (y s : ℝ) : schurGapUpper y s*schurGapLower y s = y^2 := by
  have h0 := Real.sq_sqrt (le_max_left (0 : ℝ) s)
  have h1 := Real.sq_sqrt (show 0 ≤ max 0 s+4*y^2 by positivity)
  unfold schurGapUpper schurGapLower
  nlinarith

lemma schurGapBlock_gap_sq (y s : ℝ) : (schurGapUpper y s-schurGapLower y s)^2 = max 0 s := by
  unfold schurGapUpper schurGapLower
  convert Real.sq_sqrt (le_max_left (0 : ℝ) s) using 1 <;> ring

lemma schurGapBlock_norm_measurable (x y : ℝ) (hy : 0 < y) (k : ℕ) :
    Measurable (fun s : ℝ => ‖(realSchurBlock x (schurGapUpper y s) (schurGapLower y s))^k‖^2) := by
  simp_rw [real_schur_block_hs_identity x _ _ y hy.ne' (schurGapBlock_product y _) k,
    div_pow, schurGapBlock_gap_sq]
  fun_prop

/-- Integrating the deterministic block estimate under the explicit gap
law gives a bound uniform in the power k and in the imaginary part y>0. -/
theorem schurGapBlock_power_expectation (n x y ε : ℝ) (hn : 0 < n)
    (hy : 0 < y) (hε : 0 < ε) (k : ℕ) :
    Integrable (fun s : ℝ => ‖(realSchurBlock x (schurGapUpper y s) (schurGapLower y s))^k‖^2)
      (schurSquaredGapLaw n y) ∧
    (∫ s : ℝ, ‖(realSchurBlock x (schurGapUpper y s) (schurGapLower y s))^k‖^2
      ∂schurSquaredGapLaw n y) ≤
        (2+2/(n*ε^2))*(‖(x : ℂ)+y*Complex.I‖+ε)^(2*k) := by
  haveI := schurSquaredGapLaw_probability n y hn hy
  let R := (‖(x : ℂ)+y*Complex.I‖+ε)^(2*k)
  have hi := schurSquaredGapLaw_integrable n y hn hy
  have henv : Integrable (fun s : ℝ => (2+s/ε^2)*R) (schurSquaredGapLaw n y) :=
    ((integrable_const 2).add (hi.div_const _)).mul_const _
  have hb : ∀ᵐ s ∂schurSquaredGapLaw n y,
      ‖(realSchurBlock x (schurGapUpper y s) (schurGapLower y s))^k‖^2 ≤ (2+s/ε^2)*R := by
    filter_upwards [schurSquaredGapLaw_nonnegative n y hn] with s hs
    have h := real_schur_block_hs_buffer x (schurGapUpper y s) (schurGapLower y s)
      y ε hy hε (schurGapBlock_product y s) k
    simpa only [schurGapBlock_gap_sq, max_eq_right hs] using h
  have hfi := henv.mono_nonneg (schurGapBlock_norm_measurable x y hy k).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hb
  refine ⟨hfi, (integral_mono_ae hfi henv hb).trans ?_⟩
  rw [integral_mul_const, integral_add (integrable_const 2) (hi.div_const _), integral_div]
  simp only [integral_const, probReal_univ, one_smul]
  have hm := schurSquaredGapLaw_mean_le n y hn hy
  have hh := mul_le_mul_of_nonneg_right
    (add_le_add (show (2 : ℝ) ≤ 2 from le_rfl) (div_le_div_of_nonneg_right hm (sq_nonneg ε)))
    (show 0 ≤ R by dsimp [R]; positivity)
  convert hh using 1 <;> dsimp [R] <;> ring

#print axioms schurGapBlock_power_expectation
end SpectralRadiusUpperTail
