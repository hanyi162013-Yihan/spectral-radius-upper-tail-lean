import SpectralRadiusUpperTail.RealSchurFlattenedSubexponential
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Matrix.Norms.Frobenius Topology

/-- Conditional power energy for one choice of mixed real Schur block data. -/
noncomputable def realSchurMixtureFiberMoment
    {Ω : ℕ → Type*} (n k : ℕ) (N : (n : ℕ) → Ω n → ℕ)
    (B : (n : ℕ) → (ω : Ω n) → Fin (N n ω) → RealSchurBlockData)
    (ω : Ω n) : ℝ :=
  ∫ z, ‖(flattenSchurBlocks (realSchurPaddedMatrix n (B n ω) z))^k‖^2
    ∂realSchurGlobalLaw n (B n ω)

noncomputable def realSchurMixtureBufferPower
    {Ω : ℕ → Type*} (n k : ℕ) (η : ℝ)
    (ρ : (n : ℕ) → Ω n → ℝ) (ω : Ω n) : ℝ :=
  (ρ n ω+η)^(2*k)

/-- The uniform full product-model power bound survives an arbitrary
mixture over diagonal block data and block counts. The mixture law can
depend on matrix dimension. -/
theorem real_schur_mixture_power_subexponential
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (k : ℕ → ℕ) (α η ε : ℝ) (hη : 0 < η) (hε : 0 < ε)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (hkpos : ∀ᶠ n : ℕ in atTop, 0 < k n)
    (ν : (n : ℕ) → Measure (Ω n))
    (N : (n : ℕ) → Ω n → ℕ)
    (B : (n : ℕ) → (ω : Ω n) → Fin (N n ω) → RealSchurBlockData)
    (ρ : (n : ℕ) → Ω n → ℝ)
    (hN : ∀ n ω, N n ω ≤ n)
    (hB : ∀ n ω i, realSchurDataAdmissible (B n ω i))
    (hmod : ∀ n ω i, realSchurDataRadius (B n ω i) ≤ ρ n ω)
    (hρ : ∀ n ω, 0 ≤ ρ n ω)
    (hMomentInt : ∀ n, Integrable
      (realSchurMixtureFiberMoment n (k n) N B) (ν n))
    (hPowerInt : ∀ n, Integrable
      (realSchurMixtureBufferPower n (k n) η ρ) (ν n)) :
    ∀ᶠ n : ℕ in atTop,
      (∫ ω, realSchurMixtureFiberMoment n (k n) N B ω ∂ν n) ≤
        Real.exp ((n : ℝ)*ε)*
          (∫ ω, realSchurMixtureBufferPower n (k n) η ρ ω ∂ν n) := by
  have hmodel := real_schur_flattened_power_subexponential
    k α η ε hη hε hk
  filter_upwards [hmodel, hkpos] with n hmodelN hkN
  have hpoint (ω : Ω n) :
      realSchurMixtureFiberMoment n (k n) N B ω ≤
        Real.exp ((n : ℝ)*ε)*
          realSchurMixtureBufferPower n (k n) η ρ ω := by
    exact hmodelN (N n ω) (B n ω) (ρ n ω)
      hkN (hN n ω) (hB n ω) (hmod n ω) (hρ n ω)
  have hint := integral_mono (hMomentInt n)
    ((hPowerInt n).const_mul (Real.exp ((n : ℝ)*ε))) hpoint
  simpa only [integral_const_mul] using hint

#print axioms real_schur_mixture_power_subexponential
end SpectralRadiusUpperTail
