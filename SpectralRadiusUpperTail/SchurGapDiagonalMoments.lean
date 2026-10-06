import SpectralRadiusUpperTail.SchurGapBlock
import Mathlib.MeasureTheory.Integral.Pi

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable def schurGapPowerBlock (x y : ℝ) (k : ℕ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (realSchurBlock x (schurGapUpper y s) (schurGapLower y s))^k

lemma schurGapPowerBlock_entry_measurable (x y : ℝ) (hy : 0 < y) (k : ℕ) (a b : Fin 2) :
    Measurable (fun s => schurGapPowerBlock x y k s a b) := by
  simp only [schurGapPowerBlock, real_schur_block_power_formula x _ _ y hy.ne'
    (schurGapBlock_product y _) k]
  fin_cases a <;> fin_cases b <;> simp [schurGapUpper, schurGapLower] <;> fun_prop

/-- Diagonal Schur power energies factor under the explicit independent
gap laws. The common radius R is a fixed buffer above all eigenvalue moduli. -/
theorem schur_gap_diagonal_product_bound {ι : Type*} [Fintype ι]
    (n η ρ : ℝ) (hn : 0 < n) (hη : 0 < η) (hρ : 0 ≤ ρ)
    (x y : ι → ℝ) (hy : ∀ i, 0 < y i) (m : ι → ℕ)
    (hmod : ∀ i, ‖(x i : ℂ)+y i*Complex.I‖ ≤ ρ) :
    Integrable (fun s : ι → ℝ => ∏ i, ‖schurGapPowerBlock (x i) (y i) (m i) (s i)‖^2)
      (Measure.pi (fun i => schurSquaredGapLaw n (y i))) ∧
    (∫ s : ι → ℝ, ∏ i, ‖schurGapPowerBlock (x i) (y i) (m i) (s i)‖^2
      ∂Measure.pi (fun i => schurSquaredGapLaw n (y i))) ≤
      (2+2/(n*η^2))^(Fintype.card ι)*(ρ+η)^(2*∑ i, m i) := by
  classical
  haveI (i : ι) := schurSquaredGapLaw_probability n (y i) hn (hy i)
  have hi (i : ι) := (schurGapBlock_power_expectation n (x i) (y i) η hn (hy i) hη (m i)).1
  have hb (i : ι) : (∫ s : ℝ, ‖schurGapPowerBlock (x i) (y i) (m i) s‖^2
      ∂schurSquaredGapLaw n (y i)) ≤ (2+2/(n*η^2))*(ρ+η)^(2*m i) := by
    apply (schurGapBlock_power_expectation n (x i) (y i) η hn (hy i) hη (m i)).2.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (add_le_add (hmod i) le_rfl) _
  refine ⟨Integrable.fintype_prod hi, ?_⟩
  rw [integral_fintype_prod_eq_prod (μ := fun i => schurSquaredGapLaw n (y i))
    (fun i s => ‖schurGapPowerBlock (x i) (y i) (m i) s‖^2)]
  calc
    _ ≤ ∏ i, (2+2/(n*η^2))*(ρ+η)^(2*m i) := by
      exact Finset.prod_le_prod (fun i _ => integral_nonneg (fun _ => sq_nonneg _)) (fun i _ => hb i)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ]
      rw [Finset.prod_pow_eq_pow_sum]
      simp only [Finset.mul_sum]

#print axioms schurGapPowerBlock_entry_measurable
#print axioms schur_gap_diagonal_product_bound
end SpectralRadiusUpperTail
