import SpectralRadiusUpperTail.NormalizedPowerBilinear
import SpectralRadiusUpperTail.ActualMatrixIdentity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {n : ℕ}

lemma measurable_normalizedPowerBilinear (p q : Fin n → 𝕂) (k : ℕ) :
    Measurable (normalizedPowerBilinear p q k) := by
  unfold normalizedPowerBilinear
  simp_rw [matrixPowerBilinear_smul, ← matrixBilinearPathTerm_sum]
  unfold matrixBilinearPathTerm
  fun_prop

lemma normalizedPowerBilinear_eq_normalizedArray (p q : Fin n → 𝕂) (k : ℕ)
    (x : Fin n → Fin n → 𝕂) :
    normalizedPowerBilinear p q k (fun ij => x ij.1 ij.2) =
      ∑ i, star (p i) * ((normalizedArray x)^k).mulVec q i := by
  have h : (((1/Real.sqrt (n : ℝ) : ℝ) : 𝕂) • Matrix.of x) = normalizedArray x := by
    ext i j
    simp only [normalizedArray, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul, RCLike.real_smul_eq_coe_mul]
  unfold normalizedPowerBilinear
  rw [h]

lemma measurable_normalizedArray_power_bilinear (p q : Fin n → 𝕂) (k : ℕ) :
    Measurable (fun x : Fin n → Fin n → 𝕂 =>
      ∑ i, star (p i) * ((normalizedArray x)^k).mulVec q i) := by
  have h := (measurable_normalizedPowerBilinear p q k).comp
    (show Measurable (fun x : Fin n → Fin n → 𝕂 => fun ij : Fin n × Fin n => x ij.1 ij.2) by
      fun_prop)
  simpa only [Function.comp_def, normalizedPowerBilinear_eq_normalizedArray] using h

#print axioms measurable_normalizedPowerBilinear
#print axioms normalizedPowerBilinear_eq_normalizedArray
#print axioms measurable_normalizedArray_power_bilinear
end SpectralRadiusUpperTail
