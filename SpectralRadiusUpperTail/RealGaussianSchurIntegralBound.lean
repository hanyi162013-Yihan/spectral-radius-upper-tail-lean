import SpectralRadiusUpperTail.RealGaussianConditionalSchurComparison
import SpectralRadiusUpperTail.RealSchurAtlasPowerObservables
import SpectralRadiusUpperTail.RealSchurNativeRadiusModel

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix Matrix.Norms.Frobenius ENNReal

theorem realGaussian_power_lintegral_le_of_conditional
    (n k : ℕ) (hk : 0 < k) (η C : ℝ)
    (hcond : ∀ (I : RealSchurFiniteCode n) x u,
      (∀ i, I.1.sizes i=2 → 0 < u i) →
        realSchurConditionalNativeIntegral I.1.sizes
          (fun A => ENNReal.ofReal (‖((1/Real.sqrt n) • A)^k‖^2)) x u ≤
          ENNReal.ofReal C*realSchurConditionalNativeIntegral I.1.sizes
            (fun A => ENNReal.ofReal ((max 1 (finiteRealMatrixRadius ((1/Real.sqrt n) • A))+η)^(2*k))) x u) :
    (∫⁻ a, ENNReal.ofReal (scaledFrobeniusPowerSquared (1/Real.sqrt n) k a) ∂gaussianMatrixLaw n) ≤
      ENNReal.ofReal C*(∫⁻ a, ENNReal.ofReal (realGaussianShiftedRadiusPower n k η a) ∂gaussianMatrixLaw n) := by
  let F := realSchurFiniteAtlas n
  let H₁ := fun (I : RealSchurFiniteCode n)
    (A : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ) =>
      ENNReal.ofReal (‖((1/Real.sqrt n) • A)^k‖^2)
  let H₂ := fun (I : RealSchurFiniteCode n)
    (A : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ) =>
      ENNReal.ofReal C*ENNReal.ofReal ((max 1 (finiteRealMatrixRadius ((1/Real.sqrt n) • A))+η)^(2*k))
  have hg₁ : Measurable (fun a : (Fin n × Fin n) → ℝ =>
      ENNReal.ofReal (scaledFrobeniusPowerSquared (1/Real.sqrt n) k a)) := by
    have hm : Measurable (fun a : (Fin n × Fin n) → ℝ =>
        ENNReal.ofReal (‖((1/Real.sqrt n) • entryMatrix a)^k‖^2)) :=
      (((scaled_entryMatrix_continuous (n := n) (1/Real.sqrt n)).pow k).norm.pow 2).measurable.ennreal_ofReal
    simpa only [real_frobenius_norm_sq,scaledFrobeniusPowerSquared] using hm
  have hg₂ : Measurable (fun a : (Fin n × Fin n) → ℝ =>
      ENNReal.ofReal C*ENNReal.ofReal (realGaussianShiftedRadiusPower n k η a)) :=
    measurable_const.mul (realGaussianShiftedRadiusPower_measurable n k η).ennreal_ofReal
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply realGaussian_lintegral_conditionalSchur_compare n F _ _ hg₁ hg₂ H₁ H₂
  · intro I
    dsimp only [H₁]
    fun_prop
  · intro I
    exact measurable_const.mul (realSchurNativeRadiusObservable_measurable I.1.sizes n k η)
  · intro I W hW A
    exact congrArg ENNReal.ofReal (finiteRealMatrixPower_conjugation W A hW _ k hk)
  · intro I W hW A
    exact congrArg (fun r : ℝ => ENNReal.ofReal C*ENNReal.ofReal ((max 1 r+η)^(2*k)))
      (finiteRealMatrixRadius_conjugation W A hW _)
  · intro I j t _
    exact congrArg ENNReal.ofReal (F.output_power_energy I j t _ k hk)
  · intro I j t _
    dsimp only [H₂,realGaussianShiftedRadiusPower]
    rw [F.output_radius]
  · intro I x u hu
    dsimp only [H₁,H₂]
    rw [realSchurConditionalNativeIntegral_const_mul _ _ _ ENNReal.ofReal_ne_top]
    exact hcond I x u hu

#print axioms realGaussian_power_lintegral_le_of_conditional
end SpectralRadiusUpperTail
