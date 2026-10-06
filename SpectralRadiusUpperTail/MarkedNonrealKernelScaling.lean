import SpectralRadiusUpperTail.MarkedNonrealPairDensity
import SpectralRadiusUpperTail.RealGinibreNonrealDensityAt

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

theorem markedNonrealRawKernel_scaled (m : ℕ) (z : ℂ) :
    ENNReal.ofReal (m+2 : ℝ)*markedNonrealRawKernel m (Real.sqrt (m+2 : ℝ) • z)=
      ENNReal.ofReal Real.pi*ENNReal.ofReal (realGinibreNonrealDensityAt (m+2) z) := by
  have hn : 0 < (m+2 : ℝ) := by positivity
  have hc : 0 < Real.sqrt (m+2 : ℝ) := Real.sqrt_pos.mpr hn
  have hr : ‖Real.sqrt (m+2 : ℝ) • z‖^2=(m+2 : ℝ)*‖z‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc,mul_pow,Real.sq_sqrt hn.le]
  have hi : Real.sqrt 2*|(Real.sqrt (m+2 : ℝ) • z).im|=
      Real.sqrt (2*(m+2 : ℝ))*|z.im| := by
    rw [Complex.smul_im,smul_eq_mul,abs_mul,abs_of_pos hc,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [markedNonrealRawKernel,hr,hi,realGinibreNonrealDensityAt,realGinibreNonrealDensity]
  have hindex : m+2-1=m+1 := by omega
  rw [hindex]
  push_cast
  have hcor : 0 ≤ gaussianErfcCorrection (Real.sqrt (2*(m+2 : ℝ))*|z.im|) :=
    (gaussianErfcCorrection_bounds _ (by positivity)).1
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le hcor),
    ← ENNReal.ofReal_mul hn.le,← ENNReal.ofReal_mul Real.pi_pos.le]
  congr 1
  field_simp [Real.pi_ne_zero]

#print axioms markedNonrealRawKernel_scaled
end SpectralRadiusUpperTail
