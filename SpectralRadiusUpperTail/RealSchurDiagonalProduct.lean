import SpectralRadiusUpperTail.RealSchurBlockData

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

/-- Arbitrary mixtures of real and conjugate-pair diagonal blocks obey the
same product-energy bound under their explicitly independent laws. -/
theorem real_schur_diagonal_product_bound {ι : Type*} [Fintype ι]
    (n η ρ : ℝ) (hn : 0 < n) (hη : 0 < η)
    (B : ι → RealSchurBlockData) (hB : ∀ i, realSchurDataAdmissible (B i))
    (m : ι → ℕ) (hmod : ∀ i, realSchurDataRadius (B i) ≤ ρ) :
    Integrable (fun s : ι → ℝ => ∏ i, ‖realSchurDataPower (B i) (m i) (s i)‖^2)
      (Measure.pi (fun i => realSchurDataLaw n (B i))) ∧
    (∫ s : ι → ℝ, ∏ i, ‖realSchurDataPower (B i) (m i) (s i)‖^2
      ∂Measure.pi (fun i => realSchurDataLaw n (B i))) ≤
      (2+2/(n*η^2))^(Fintype.card ι)*(ρ+η)^(2*∑ i, m i) := by
  classical
  haveI (i : ι) := realSchurDataLaw_probability n hn (B i) (hB i)
  have hh (i : ι) := realSchurDataPower_second_moment n η ρ hn hη (B i) (hB i) (hmod i) (m i)
  refine ⟨Integrable.fintype_prod (fun i => (hh i).1), ?_⟩
  rw [integral_fintype_prod_eq_prod (μ := fun i => realSchurDataLaw n (B i))
    (fun i s => ‖realSchurDataPower (B i) (m i) s‖^2)]
  calc
    _ ≤ ∏ i, (2+2/(n*η^2))*(ρ+η)^(2*m i) :=
      Finset.prod_le_prod (fun i _ => integral_nonneg (fun _ => sq_nonneg _))
        (fun i _ => (hh i).2)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ]
      rw [Finset.prod_pow_eq_pow_sum]
      simp only [Finset.mul_sum]

#print axioms real_schur_diagonal_product_bound
end SpectralRadiusUpperTail
