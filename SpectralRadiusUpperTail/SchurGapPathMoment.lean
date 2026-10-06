import SpectralRadiusUpperTail.SchurGapDiagonalMoments
import SpectralRadiusUpperTail.GaussianBridgeRandomDiagonal

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

/-- The explicit independent gap/bridge law for one path of real 2x2
Schur blocks. This is not the law of an entire Gaussian Schur decomposition. -/
noncomputable def schurGapPathLaw (n : ℝ) (l : ℕ) (y : Fin (l+1) → ℝ) :
    Measure ((Fin (l+1) → ℝ) × GaussianBridgeSpace 2 l) :=
  (Measure.pi (fun i => schurSquaredGapLaw n (y i))).prod (gaussianBridgeLaw 2 l)

noncomputable def schurGapPathProduct (n l : ℕ) (x y : Fin (l+1) → ℝ)
    (m : Fin (l+1) → ℕ) (z : (Fin (l+1) → ℝ) × GaussianBridgeSpace 2 l) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  gaussianBridgeProduct (1/Real.sqrt n) l (fun i => schurGapPowerBlock (x i) (y i) (m i) (z.1 i)) z.2

/-- A full single-path estimate under its explicit independent block law,
including integrability, normalization, and every diagonal waiting power. -/
theorem schur_gap_path_second_moment (n l : ℕ) (hn : 0 < n)
    (η ρ : ℝ) (hη : 0 < η) (hρ : 0 ≤ ρ) (x y : Fin (l+1) → ℝ)
    (hy : ∀ i, 0 < y i) (m : Fin (l+1) → ℕ)
    (hmod : ∀ i, ‖(x i : ℂ)+y i*Complex.I‖ ≤ ρ) :
    Integrable (fun z => ‖schurGapPathProduct n l x y m z‖^2) (schurGapPathLaw n l y) ∧
    (∫ z, ‖schurGapPathProduct n l x y m z‖^2 ∂schurGapPathLaw n l y) ≤
      (1/(n : ℝ))^l*(2+2/((n : ℝ)*η^2))^(l+1)*(ρ+η)^(2*∑ i, m i) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  haveI (i : Fin (l+1)) := schurSquaredGapLaw_probability (n : ℝ) (y i) hnR (hy i)
  have hd := schur_gap_diagonal_product_bound (n : ℝ) η ρ hnR hη hρ x y hy m hmod
  have hh := gaussian_bridge_random_diagonal_moment
    (Measure.pi (fun i => schurSquaredGapLaw n (y i))) (1/Real.sqrt n) l
    (fun i (s : Fin (l+1) → ℝ) => schurGapPowerBlock (x i) (y i) (m i) (s i))
    (fun i a b => (schurGapPowerBlock_entry_measurable (x i) (y i) (hy i) (m i) a b).comp
      (measurable_pi_apply i)) hd.1
  refine ⟨hh.1, ?_⟩
  change (∫ z, ‖gaussianBridgeProduct (1/Real.sqrt n) l
    (fun i => schurGapPowerBlock (x i) (y i) (m i) (z.1 i)) z.2‖^2
    ∂(Measure.pi (fun i => schurSquaredGapLaw n (y i))).prod (gaussianBridgeLaw 2 l)) ≤ _
  rw [hh.2]
  have hscale : (1/Real.sqrt n)^2 = 1/(n : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt hnR.le]
  rw [hscale]
  have hb := mul_le_mul_of_nonneg_left hd.2 (show 0 ≤ (1/(n : ℝ))^l by positivity)
  simpa only [Fintype.card_fin, mul_assoc] using hb

#print axioms schur_gap_path_second_moment
end SpectralRadiusUpperTail
