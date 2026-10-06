import SpectralRadiusUpperTail.RealSchurStrictUpperConjugation
import SpectralRadiusUpperTail.RealArrayEnergyIsometry

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix BigOperators ENNReal

noncomputable def realSchurMixedStrictUpperConjugationEquiv
    {m : ℕ} (s : Fin m → ℕ)
    (W : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) (hW : Wᵀ*W=1)
    (hoff : ∀ i j : RealSchurMixedCoord s, i.1 ≠ j.1 → W i j=0) :
    (RealSchurMixedStrictUpperEntry s → ℝ) ≃ₗ[ℝ] (RealSchurMixedStrictUpperEntry s → ℝ) := by
  have hWt : Wᵀᵀ*Wᵀ=1 := by simpa only [Matrix.transpose_transpose] using mul_eq_one_comm.mp hW
  have hofft : ∀ i j : RealSchurMixedCoord s, i.1 ≠ j.1 → Wᵀ i j=0 :=
    fun i j h => hoff j i h.symm
  exact {
    realSchurMixedStrictUpperConjugationLinear s W with
    invFun := realSchurMixedStrictUpperConjugationLinear s Wᵀ
    left_inv := realSchurMixedStrictUpperConjugation_inverse s W hW hoff
    right_inv := fun u => by
      change realSchurMixedStrictUpperConjugationLinear s W
        (realSchurMixedStrictUpperConjugationLinear s Wᵀ u)=u
      simpa only [Matrix.transpose_transpose] using
        realSchurMixedStrictUpperConjugation_inverse s Wᵀ hWt hofft u }

theorem realSchurMixedStrictUpperConjugation_energy
    {m : ℕ} (s : Fin m → ℕ)
    (W : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) (hW : Wᵀ*W=1)
    (hoff : ∀ i j : RealSchurMixedCoord s, i.1 ≠ j.1 → W i j=0)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    (∑ p, (realSchurMixedStrictUpperConjugationEquiv s W hW hoff u p)^2) =
      ∑ p, (u p)^2 := by
  have h := realMatrixGaussianWeight_orthogonal_conjugation
    (RealSchurMixedCoord s) W (realSchurMixedUpperEntryJoin s 0 u) hW
  rw [← realSchurMixedStrictUpperConjugation_embed s W hoff u,
    realSchurMixedGaussianWeight_join,realSchurMixedGaussianWeight_join] at h
  simp only [Pi.zero_apply,zero_pow (by decide : (2 : ℕ) ≠ 0),Finset.sum_const_zero,
    neg_zero,zero_div,Real.exp_zero,one_mul] at h
  have he := Real.exp_injective h
  change (∑ p, (realSchurMixedStrictUpperConjugationLinear s W u p)^2)=∑ p, (u p)^2
  linarith

/-- Every blockwise orthogonal rotation preserves the complete
strict-upper Gaussian integral, with no truncation or density factor. -/
theorem realSchurMixedStrictUpperGaussian_conjugation
    {m : ℕ} (s : Fin m → ℕ)
    (W : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) (hW : Wᵀ*W=1)
    (hoff : ∀ i j : RealSchurMixedCoord s, i.1 ≠ j.1 → W i j=0)
    (g : (RealSchurMixedStrictUpperEntry s → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ u, ENNReal.ofReal (Real.exp (-(∑ p, (u p)^2)/2)) *
      g (realSchurMixedStrictUpperConjugationEquiv s W hW hoff u)) =
      ∫⁻ u, ENNReal.ofReal (Real.exp (-(∑ p, (u p)^2)/2)) * g u :=
  realArrayGaussian_lintegral_energyEquiv
    (realSchurMixedStrictUpperConjugationEquiv s W hW hoff)
    (realSchurMixedStrictUpperConjugation_energy s W hW hoff) g hg

#print axioms realSchurMixedStrictUpperConjugationEquiv
#print axioms realSchurMixedStrictUpperConjugation_energy
#print axioms realSchurMixedStrictUpperGaussian_conjugation
end SpectralRadiusUpperTail
