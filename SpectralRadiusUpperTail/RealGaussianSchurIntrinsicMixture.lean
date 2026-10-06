import SpectralRadiusUpperTail.RealGaussianSchurMixtureConditional
import SpectralRadiusUpperTail.RealSchurDataIntrinsicRadius
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

noncomputable def realSchurIntrinsicRadiusFamily
    {Ω : ℕ → Type*}
    (N : (n : ℕ) → Ω n → ℕ)
    (B : (n : ℕ) → (ω : Ω n) → Fin (N n ω) → RealSchurBlockData)
    (n : ℕ) (ω : Ω n) : ℝ :=
  realSchurDataIntrinsicRadius (B n ω)

/-- The actual Gaussian Schur-distribution gap can be stated using only
the intrinsic diagonal-block radius. Its positivity, domination of every
block radius, and independence from the product-model bridge coordinates
are all proved rather than assumed. -/
theorem gaussianSchurPowerComparisonInput_of_intrinsic_mixture
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (ν : (n : ℕ) → Measure (Ω n))
    (N : (n : ℕ) → Ω n → ℕ)
    (B : (n : ℕ) → (ω : Ω n) → Fin (N n ω) → RealSchurBlockData)
    (hN : ∀ n ω, N n ω ≤ n)
    (hB : ∀ n ω i, realSchurDataAdmissible (B n ω i))
    (hMomentInt : ∀ n k, Integrable
      (realSchurMixtureFiberMoment n k N B) (ν n))
    (hPowerInt : ∀ n k η, 0 < η → Integrable
      (realSchurMixtureBufferPower n k η
        (realSchurIntrinsicRadiusFamily N B)) (ν n))
    (hGaussianMoment : ∀ n k,
      gaussianPowerMoment n k ≤
        (∫ ω, realSchurMixtureFiberMoment n k N B ω ∂ν n))
    (hRadius : ∀ n k η, 0 < η →
      (∫ ω, realSchurMixtureBufferPower n k η
        (realSchurIntrinsicRadiusFamily N B) ω ∂ν n) ≤
        (∫ x, realGaussianShiftedRadiusPower n k η x
          ∂gaussianMatrixLaw n)) :
    GaussianSchurPowerComparisonInput := by
  apply gaussianSchurPowerComparisonInput_of_mixture ν N B
    (realSchurIntrinsicRadiusFamily N B)
    hN hB
  · intro n ω i
    exact realSchurDataRadius_le_intrinsic (B n ω) i
  · intro n ω
    exact realSchurDataIntrinsicRadius_nonneg (B n ω)
  · exact hMomentInt
  · exact hPowerInt
  · exact hGaussianMoment
  · exact hRadius

#print axioms gaussianSchurPowerComparisonInput_of_intrinsic_mixture
end SpectralRadiusUpperTail
