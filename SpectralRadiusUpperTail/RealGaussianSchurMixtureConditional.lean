import SpectralRadiusUpperTail.RealSchurMixtureMoment
import SpectralRadiusUpperTail.RealGaussianSchurPowerConditional
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Matrix.Norms.Frobenius Topology

/-- The checked full Schur product-model moment estimate transfers to the
actual Gaussian comparison once its conditional law is represented as a
mixture of those product models and their diagonal radii. The two
representation inequalities below are the remaining finite-dimensional
Schur-distribution work; they are not asserted for Gaussian matrices here. -/
theorem gaussianSchurPowerComparisonInput_of_mixture
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (ν : (n : ℕ) → Measure (Ω n))
    (N : (n : ℕ) → Ω n → ℕ)
    (B : (n : ℕ) → (ω : Ω n) → Fin (N n ω) → RealSchurBlockData)
    (ρ : (n : ℕ) → Ω n → ℝ)
    (hN : ∀ n ω, N n ω ≤ n)
    (hB : ∀ n ω i, realSchurDataAdmissible (B n ω i))
    (hmod : ∀ n ω i, realSchurDataRadius (B n ω i) ≤ ρ n ω)
    (hρ : ∀ n ω, 0 ≤ ρ n ω)
    (hMomentInt : ∀ n k, Integrable
      (realSchurMixtureFiberMoment n k N B) (ν n))
    (hPowerInt : ∀ n k η, 0 < η → Integrable
      (realSchurMixtureBufferPower n k η ρ) (ν n))
    (hGaussianMoment : ∀ n k,
      gaussianPowerMoment n k ≤
        (∫ ω, realSchurMixtureFiberMoment n k N B ω ∂ν n))
    (hRadius : ∀ n k η, 0 < η →
      (∫ ω, realSchurMixtureBufferPower n k η ρ ω ∂ν n) ≤
        (∫ x, realGaussianShiftedRadiusPower n k η x
          ∂gaussianMatrixLaw n)) :
    GaussianSchurPowerComparisonInput := by
  intro α hα η hη ε hε
  let k : ℕ → ℕ := fun n => ⌊α*(n : ℝ)⌋₊
  have hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α) :=
    floor_linear_power_ratio α hα
  have hkpos : ∀ᶠ n : ℕ in atTop, 0 < k n := by
    have hklower : ∀ᶠ n : ℕ in atTop,
        α/2 < (k n : ℝ)/(n : ℝ) :=
      (tendsto_order.mp hk).1 (α/2) (by linarith)
    filter_upwards [hklower, eventually_gt_atTop 0] with n hl hn
    by_contra hzero
    have hz : k n = 0 := by omega
    simp [hz] at hl
    linarith
  have hmixture := real_schur_mixture_power_subexponential
    k α η ε hη hε hk hkpos ν N B ρ hN hB hmod hρ
    (fun n => hMomentInt n (k n))
    (fun n => hPowerInt n (k n) η hη)
  filter_upwards [hmixture] with n hn
  change gaussianPowerMoment n (k n) ≤
    Real.exp ((n : ℝ)*ε)*
      (∫ x, realGaussianShiftedRadiusPower n (k n) η x
        ∂gaussianMatrixLaw n)
  calc
    gaussianPowerMoment n (k n) ≤
        (∫ ω, realSchurMixtureFiberMoment n (k n) N B ω ∂ν n) :=
      hGaussianMoment n (k n)
    _ ≤ Real.exp ((n : ℝ)*ε)*
        (∫ ω, realSchurMixtureBufferPower n (k n) η ρ ω ∂ν n) := hn
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hRadius n (k n) η hη) (Real.exp_pos _).le

#print axioms gaussianSchurPowerComparisonInput_of_mixture
end SpectralRadiusUpperTail
