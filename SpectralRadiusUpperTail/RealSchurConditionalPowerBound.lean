import SpectralRadiusUpperTail.RealSchurNativePowerTransport
import SpectralRadiusUpperTail.RealSchurNativeRadiusModel
import SpectralRadiusUpperTail.RealSchurFlattenedSubexponential

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Matrix Matrix.Norms.Frobenius ENNReal Topology

theorem realSchurConditionalNative_power_le {m : ℕ}
    (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (hsmall : ∀ i, s i ≤ 2)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hm : m ≤ n)
    (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C) (x u : Fin m → ℝ)
    (hu : ∀ i, s i=2 → 0 < u i)
    (hbound : (∫ z, ‖(flattenSchurBlocks (realSchurPaddedMatrix n
      (fun i => realSchurNativeBlockData (s i) (x i/Real.sqrt n) (u i/(n : ℝ))) z))^k‖^2
      ∂realSchurGlobalLaw n
        (fun i => realSchurNativeBlockData (s i) (x i/Real.sqrt n) (u i/(n : ℝ)))) ≤
      C*(max 1 (realSchurDataIntrinsicRadius
        (fun i => realSchurNativeBlockData (s i) (x i/Real.sqrt n) (u i/(n : ℝ))))+η)^(2*k)) :
    realSchurConditionalNativeIntegral s
      (fun A => ENNReal.ofReal (‖((1/Real.sqrt n) • A)^k‖^2)) x u ≤
      ENNReal.ofReal C*realSchurConditionalNativeIntegral s
        (fun A => ENNReal.ofReal ((max 1 (finiteRealMatrixRadius ((1/Real.sqrt n) • A))+η)^(2*k))) x u := by
  let B := fun i => realSchurNativeBlockData (s i) (x i/Real.sqrt n) (u i/(n : ℝ))
  let ρ := max 1 (realSchurDataIntrinsicRadius B)
  have hρ : 0 ≤ ρ := le_trans (by norm_num) (le_max_left _ _)
  have hB : ∀ i, realSchurDataAdmissible (B i) := fun i =>
    realSchurNativeBlockData_admissible _ _ _ (fun hi => div_pos (hu i hi) (Nat.cast_pos.mpr hn))
  have hmod : ∀ i, realSchurDataRadius (B i) ≤ ρ := fun i =>
    (realSchurDataRadius_le_intrinsic B i).trans (le_max_right _ _)
  have hi := (real_schur_flattened_power_second_moment_bound n k hn hk hm η ρ hη
    (add_pos_of_nonneg_of_pos hρ hη) B hB hmod).1
  rw [realSchurConditionalNative_power_model s hs hsmall n k hn hk x u hu,
    realSchurConditionalNative_radius_model s hs hsmall n k hn η x u hu]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  calc
    _ ≤ realSchurUpperGaussianMass s*ENNReal.ofReal (C*(ρ+η)^(2*k)) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hbound)
    _ = _ := by rw [ENNReal.ofReal_mul hC]; dsimp only [ρ,B]; ac_rfl

/-- Uniform conditional comparison for the actual Schur integral; all
probabilistic identification and block-padding work has been discharged. -/
theorem realSchurConditionalNative_power_subexponential
    (k : ℕ → ℕ) (α η ε : ℝ) (hη : 0 < η) (hε : 0 < ε)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α)) :
    ∀ᶠ n : ℕ in atTop, ∀ (m : ℕ) (s : Fin m → ℕ),
      (∀ i, s i=1 ∨ s i=2) → m ≤ n → 0 < k n →
      ∀ x u : Fin m → ℝ, (∀ i, s i=2 → 0 < u i) →
        realSchurConditionalNativeIntegral s
          (fun A => ENNReal.ofReal (‖((1/Real.sqrt n) • A)^(k n)‖^2)) x u ≤
          ENNReal.ofReal (Real.exp ((n : ℝ)*ε))*realSchurConditionalNativeIntegral s
            (fun A => ENNReal.ofReal ((max 1 (finiteRealMatrixRadius ((1/Real.sqrt n) • A))+η)^(2*k n))) x u := by
  filter_upwards [real_schur_flattened_power_subexponential k α η ε hη hε hk,
    eventually_gt_atTop 0] with n hmodel hn m s hs hm hk0 x u hu
  have hsmall : ∀ i, s i ≤ 2 := by intro i; rcases hs i with h | h <;> omega
  apply realSchurConditionalNative_power_le s hs hsmall n (k n) hn hk0 hm η _ hη
    (Real.exp_pos _).le x u hu
  apply hmodel m _ _ hk0 hm
  · intro i
    exact realSchurNativeBlockData_admissible _ _ _ (fun hi => div_pos (hu i hi) (Nat.cast_pos.mpr hn))
  · intro i
    exact (realSchurDataRadius_le_intrinsic
      (fun j => realSchurNativeBlockData (s j) (x j/Real.sqrt n) (u j/(n : ℝ))) i).trans (le_max_right _ _)
  · exact le_trans (by norm_num) (le_max_left _ _)

#print axioms realSchurConditionalNative_power_le
#print axioms realSchurConditionalNative_power_subexponential
end SpectralRadiusUpperTail
