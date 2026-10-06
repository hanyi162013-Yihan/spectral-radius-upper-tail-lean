import SpectralRadiusUpperTail.RealGaussianShiftedRadiusMoment
import SpectralRadiusUpperTail.RealGaussianWeightedRadiusConditional
import SpectralRadiusUpperTail.RealUpperFromGaussianPower
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The distributional Schur transfer still to be proved for the actual
real Gaussian matrix. The explicit product-model calculation supplies the
right-hand power bound but has not yet been identified with this law. -/
def GaussianSchurPowerComparisonInput : Prop :=
  ∀ α : ℝ, 0 < α → ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      gaussianPowerMoment n ⌊α*(n : ℝ)⌋₊ ≤
        Real.exp ((n : ℝ)*ε) *
          (∫ x, realGaussianShiftedRadiusPower n
            ⌊α*(n : ℝ)⌋₊ η x ∂gaussianMatrixLaw n)

/-- The remaining real Gaussian Hilbert--Schmidt power input follows from
two explicit finite-dimensional facts: weighted one-point identities and
the actual conditional Schur transfer. -/
theorem gaussianPowerUpperInput_of_onePoint_and_schur
    (hroot : ∀ n k, 3 ≤ n →
      Integrable (realGaussianExteriorRootPower n k)
        (gaussianMatrixLaw n))
    (hidentity : ∀ n k, 3 ≤ n →
      (∫ x, realGaussianExteriorRootPower n k x
        ∂gaussianMatrixLaw n) ≤
          realGinibreWeightedOnePointEnvelope n k)
    (hSchur : GaussianSchurPowerComparisonInput) :
    GaussianPowerUpperInput := by
  intro α hα δ hδ
  let ε : ℝ := δ/4
  let η : ℝ := δ/(8*(α+1))
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hlog0 : 0 ≤ Real.log (1+η) :=
    Real.log_nonneg (by linarith)
  have hlogη : Real.log (1+η) ≤ η := by
    have hh := Real.log_le_sub_one_of_pos
      (by linarith : 0 < 1+η)
    linarith
  have hk := floor_linear_power_ratio α hα
  have hkbound : ∀ᶠ n : ℕ in atTop,
      (⌊α*(n : ℝ)⌋₊ : ℝ)/(n : ℝ) < α+1 :=
    (tendsto_order.mp hk).2 (α+1) (by linarith)
  have hclip := realGaussianClippedRadiusPower_upper_of_onePoint
    hroot hidentity (fun n => ⌊α*(n : ℝ)⌋₊) α hα hk ε hε
  have hSchurEv := hSchur α hα η hη ε hε
  filter_upwards [hkbound, hclip, hSchurEv,
    eventually_ge_atTop 3] with n hkn hclipN hSchurN hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hkn' : (⌊α*(n : ℝ)⌋₊ : ℝ) ≤ (α+1)*(n : ℝ) :=
    ((div_lt_iff₀ hnR).mp hkn).le
  have hmul := mul_le_mul_of_nonneg_right hkn' hlog0
  have hscale : 0 ≤ 2*(α+1)*(n : ℝ) := by positivity
  have hmul2 := mul_le_mul_of_nonneg_left hlogη hscale
  have harg : 2*(⌊α*(n : ℝ)⌋₊ : ℝ)*Real.log (1+η) ≤
      (n : ℝ)*ε := by
    have harg1 : 2*(⌊α*(n : ℝ)⌋₊ : ℝ)*Real.log (1+η) ≤
        2*(α+1)*(n : ℝ)*Real.log (1+η) := by nlinarith [hmul]
    have heq : 2*(α+1)*(n : ℝ)*η = (n : ℝ)*ε := by
      dsimp [η, ε]
      have ha : α+1 ≠ 0 := by linarith
      field_simp [ha]
      ring
    exact harg1.trans (hmul2.trans_eq heq)
  have hpoweq : (1+η)^(2*⌊α*(n : ℝ)⌋₊) =
      Real.exp (2*(⌊α*(n : ℝ)⌋₊ : ℝ)*Real.log (1+η)) := by
    rw [show 2*(⌊α*(n : ℝ)⌋₊ : ℝ) =
        ((2*⌊α*(n : ℝ)⌋₊ : ℕ) : ℝ) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by linarith : 0 < 1+η)]
  have hfactor : (1+η)^(2*⌊α*(n : ℝ)⌋₊) ≤
      Real.exp ((n : ℝ)*ε) := by
    rw [hpoweq]
    exact Real.exp_le_exp.mpr harg
  have hclip0 : 0 ≤
      (∫ x, realGaussianClippedRadiusPower n
        ⌊α*(n : ℝ)⌋₊ x ∂gaussianMatrixLaw n) := by
    apply integral_nonneg
    intro x
    unfold realGaussianClippedRadiusPower
    exact pow_nonneg
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)) _
  have hshift := realGaussianShiftedRadiusPower_integral_le n
    ⌊α*(n : ℝ)⌋₊ hnpos η hη.le
    (hroot n ⌊α*(n : ℝ)⌋₊ hn)
  calc
    gaussianPowerMoment n ⌊α*(n : ℝ)⌋₊ ≤
        Real.exp ((n : ℝ)*ε) *
          (∫ x, realGaussianShiftedRadiusPower n
            ⌊α*(n : ℝ)⌋₊ η x ∂gaussianMatrixLaw n) := hSchurN
    _ ≤ Real.exp ((n : ℝ)*ε) *
        ((1+η)^(2*⌊α*(n : ℝ)⌋₊) *
          (∫ x, realGaussianClippedRadiusPower n
            ⌊α*(n : ℝ)⌋₊ x ∂gaussianMatrixLaw n)) :=
      mul_le_mul_of_nonneg_left hshift (Real.exp_pos _).le
    _ ≤ Real.exp ((n : ℝ)*ε) *
        (Real.exp ((n : ℝ)*ε) *
          (∫ x, realGaussianClippedRadiusPower n
            ⌊α*(n : ℝ)⌋₊ x ∂gaussianMatrixLaw n)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hfactor hclip0)
        (Real.exp_pos _).le
    _ ≤ Real.exp ((n : ℝ)*ε) *
        (Real.exp ((n : ℝ)*ε) *
          Real.exp ((n : ℝ)*(powerRate 1 α+ε))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hclipN (Real.exp_pos _).le)
        (Real.exp_pos _).le
    _ = Real.exp ((n : ℝ)*(powerRate 1 α+3*ε)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
      apply Real.exp_le_exp.mpr
      dsimp [ε]
      nlinarith

#print axioms gaussianPowerUpperInput_of_onePoint_and_schur
end SpectralRadiusUpperTail
