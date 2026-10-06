import SpectralRadiusUpperTail.RealSchurDiagonalProduct
import SpectralRadiusUpperTail.GaussianBridgeRandomDiagonal

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

/-- Explicit independent mixed Schur block laws along one path. -/
noncomputable def realSchurPathLaw (n : ℝ) (l : ℕ) (B : Fin (l+1) → RealSchurBlockData) :
    Measure ((Fin (l+1) → ℝ) × GaussianBridgeSpace 2 l) :=
  (Measure.pi (fun i => realSchurDataLaw n (B i))).prod (gaussianBridgeLaw 2 l)

noncomputable def realSchurPathProduct (n l : ℕ) (B : Fin (l+1) → RealSchurBlockData)
    (m : Fin (l+1) → ℕ) (z : (Fin (l+1) → ℝ) × GaussianBridgeSpace 2 l) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  gaussianBridgeProduct (1/Real.sqrt n) l (fun i => realSchurDataPower (B i) (m i) (z.1 i)) z.2

lemma realSchurPathProduct_entry_measurable (n l : ℕ) (B : Fin (l+1) → RealSchurBlockData)
    (hB : ∀ i, realSchurDataAdmissible (B i)) (m : Fin (l+1) → ℕ) (a b : Fin 2) :
    Measurable (fun z => realSchurPathProduct n l B m z a b) := by
  exact gaussianBridgeProduct_parametric_entry_measurable (1/Real.sqrt n) l
    (fun i (z : (Fin (l+1) → ℝ) × GaussianBridgeSpace 2 l) =>
      realSchurDataPower (B i) (m i) (z.1 i)) Prod.snd measurable_snd
    (fun i a b => (realSchurDataPower_entry_measurable (B i) (hB i) (m i) a b).comp
      ((measurable_pi_apply i).comp measurable_fst)) a b

/-- The single-path moment bound includes any mixture of real 1x1 and
conjugate-pair 2x2 blocks. It is a theorem of the explicit product model,
not an identification of the conditional law of a Gaussian matrix. -/
theorem real_schur_path_second_moment (n l : ℕ) (hn : 0 < n)
    (η ρ : ℝ) (hη : 0 < η) (B : Fin (l+1) → RealSchurBlockData)
    (hB : ∀ i, realSchurDataAdmissible (B i)) (m : Fin (l+1) → ℕ)
    (hmod : ∀ i, realSchurDataRadius (B i) ≤ ρ) :
    Integrable (fun z => ‖realSchurPathProduct n l B m z‖^2) (realSchurPathLaw n l B) ∧
    (∫ z, ‖realSchurPathProduct n l B m z‖^2 ∂realSchurPathLaw n l B) ≤
      (1/(n : ℝ))^l*(2+2/((n : ℝ)*η^2))^(l+1)*(ρ+η)^(2*∑ i, m i) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  haveI (i : Fin (l+1)) := realSchurDataLaw_probability (n : ℝ) hnR (B i) (hB i)
  have hd := real_schur_diagonal_product_bound (n : ℝ) η ρ hnR hη B hB m hmod
  have hh := gaussian_bridge_random_diagonal_moment
    (Measure.pi (fun i => realSchurDataLaw n (B i))) (1/Real.sqrt n) l
    (fun i (s : Fin (l+1) → ℝ) => realSchurDataPower (B i) (m i) (s i))
    (fun i a b => (realSchurDataPower_entry_measurable (B i) (hB i) (m i) a b).comp
      (measurable_pi_apply i)) hd.1
  refine ⟨hh.1, ?_⟩
  change (∫ z, ‖gaussianBridgeProduct (1/Real.sqrt n) l
    (fun i => realSchurDataPower (B i) (m i) (z.1 i)) z.2‖^2
    ∂(Measure.pi (fun i => realSchurDataLaw n (B i))).prod (gaussianBridgeLaw 2 l)) ≤ _
  rw [hh.2]
  have hscale : (1/Real.sqrt n)^2 = 1/(n : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt hnR.le]
  rw [hscale]
  have hb := mul_le_mul_of_nonneg_left hd.2 (show 0 ≤ (1/(n : ℝ))^l by positivity)
  simpa only [Fintype.card_fin, mul_assoc] using hb

#print axioms realSchurPathProduct_entry_measurable
#print axioms real_schur_path_second_moment
end SpectralRadiusUpperTail
