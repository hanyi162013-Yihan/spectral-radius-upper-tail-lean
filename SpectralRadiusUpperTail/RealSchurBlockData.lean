import SpectralRadiusUpperTail.SchurGapDiagonalMoments

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Frobenius

/-- Eigenvalue data for a real Schur diagonal block. A real block is 1x1;
a conjugate pair is 2x2 and requires a positive imaginary part. -/
inductive RealSchurBlockData where
  | real (value : ℝ)
  | pair (re im : ℝ)

def realSchurDataAdmissible : RealSchurBlockData → Prop
  | .real _ => True
  | .pair _ y => 0 < y

noncomputable def realSchurDataRadius : RealSchurBlockData → ℝ
  | .real x => |x|
  | .pair x y => ‖(x : ℂ)+y*Complex.I‖

noncomputable def realSchurDataLaw (n : ℝ) : RealSchurBlockData → Measure ℝ
  | .real _ => Measure.dirac 0
  | .pair _ y => schurSquaredGapLaw n y

/-- Powers are padded AFTER taking the power in the original block.
In particular a 1x1 block's zeroth power is diag(1,0), not the 2x2 identity. -/
noncomputable def realSchurDataPower : RealSchurBlockData → ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℝ
  | .real x, k, _ => !![x^k, 0; 0, 0]
  | .pair x y, k, s => schurGapPowerBlock x y k s

lemma realSchurDataPower_real_norm (x s : ℝ) (k : ℕ) :
    ‖realSchurDataPower (.real x) k s‖^2 = |x|^(2*k) := by
  have hn : ‖realSchurDataPower (.real x) k s‖^2 = (x^k)^2 := by
    rw [real_frobenius_norm_sq]
    simp [realSchurDataPower, Fin.sum_univ_two]
  rw [hn]
  calc
    _ = |x^k|^2 := (sq_abs _).symm
    _ = _ := by rw [abs_pow, ← pow_mul, Nat.mul_comm k 2]

lemma realSchurDataPower_add (B : RealSchurBlockData) (p q : ℕ) (s : ℝ) :
    realSchurDataPower B (p+q) s = realSchurDataPower B p s*realSchurDataPower B q s := by
  cases B with
  | real x =>
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realSchurDataPower, Matrix.mul_apply, Fin.sum_univ_two, pow_add]
  | pair x y => exact pow_add _ _ _

lemma realSchurDataLaw_probability (n : ℝ) (hn : 0 < n) (B : RealSchurBlockData)
    (hB : realSchurDataAdmissible B) : IsProbabilityMeasure (realSchurDataLaw n B) := by
  cases B with
  | real x => change IsProbabilityMeasure (Measure.dirac (0 : ℝ)); infer_instance
  | pair x y => exact schurSquaredGapLaw_probability n y hn hB

lemma realSchurDataPower_entry_measurable (B : RealSchurBlockData)
    (hB : realSchurDataAdmissible B) (k : ℕ) (a b : Fin 2) :
    Measurable (fun s => realSchurDataPower B k s a b) := by
  cases B with
  | real x => exact measurable_const
  | pair x y => exact schurGapPowerBlock_entry_measurable x y hB k a b

/-- One uniform bound handles real 1x1 and conjugate-pair 2x2 blocks. -/
theorem realSchurDataPower_second_moment (n η ρ : ℝ) (hn : 0 < n) (hη : 0 < η)
    (B : RealSchurBlockData) (hB : realSchurDataAdmissible B)
    (hmod : realSchurDataRadius B ≤ ρ) (k : ℕ) :
    Integrable (fun s => ‖realSchurDataPower B k s‖^2) (realSchurDataLaw n B) ∧
    (∫ s, ‖realSchurDataPower B k s‖^2 ∂realSchurDataLaw n B) ≤
      (2+2/(n*η^2))*(ρ+η)^(2*k) := by
  cases B with
  | real x =>
    simp_rw [realSchurDataPower_real_norm]
    change Integrable (fun _ : ℝ => |x|^(2*k)) (Measure.dirac 0) ∧
      (∫ _ : ℝ, |x|^(2*k) ∂Measure.dirac 0) ≤ (2+2/(n*η^2))*(ρ+η)^(2*k)
    refine ⟨integrable_const _, ?_⟩
    simp only [integral_const, probReal_univ, one_smul]
    have hR : |x| ≤ ρ+η := by change |x| ≤ ρ at hmod; linarith
    have hp := pow_le_pow_left₀ (abs_nonneg x) hR (2*k)
    have hR0 : 0 ≤ ρ+η := (abs_nonneg x).trans hR
    have hC : 1 ≤ 2+2/(n*η^2) := by
      have hh : 0 ≤ 2/(n*η^2) := by positivity
      linarith
    exact hp.trans (le_mul_of_one_le_left (pow_nonneg hR0 _) hC)
  | pair x y =>
    have hh := schurGapBlock_power_expectation n x y η hn hB hη k
    refine ⟨hh.1, hh.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (show 0 ≤ ‖(x : ℂ)+y*Complex.I‖+η by positivity)
      (add_le_add hmod le_rfl) _

#print axioms realSchurDataPower_add
#print axioms realSchurDataPower_second_moment
end SpectralRadiusUpperTail
