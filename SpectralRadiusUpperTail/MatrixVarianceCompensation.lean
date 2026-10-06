import SpectralRadiusUpperTail.MatrixSpectralOrder
import Mathlib.Tactic.Module

namespace SpectralRadiusUpperTail
open scoped ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

lemma matrix_affine_spectrum {Y : Matrix ι ι 𝕂} (hY : Y.IsHermitian)
    (s c : ℝ) {l : ℝ} (hl : l ∈ spectrum ℝ Y) :
    s*l-c ∈ spectrum ℝ (s • Y-algebraMap ℝ (Matrix ι ι 𝕂) c) := by
  have hY' : IsSelfAdjoint Y := hY
  have he : cfc (fun x : ℝ => s*x-c) Y = s • Y-algebraMap ℝ (Matrix ι ι 𝕂) c := by
    rw [cfc_sub (fun x : ℝ => s*x) (fun _ => c) Y, cfc_const_mul_id s Y hY', cfc_const c Y hY']
  rw [← he, cfc_map_spectrum (fun x : ℝ => s*x-c) Y hY']
  exact ⟨l, hl, rfl⟩

/-- Removing a norm-bounded Hermitian compensation shifts a spectral threshold
by at most its deterministic scalar bound. -/
theorem matrix_variance_compensation {Y D : Matrix ι ι 𝕂}
    (hY : Y.IsHermitian) (hD : D.IsHermitian) {s q v t : ℝ}
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hv : ‖D‖ ≤ v)
    (ht : ∃ l ∈ spectrum ℝ Y, t ≤ l) :
    ∃ r ∈ spectrum ℝ (s • Y-q • D), s*t-q*v ≤ r := by
  obtain ⟨l, hl, htl⟩ := ht
  have hbound := matrix_le_scalar_of_norm hD hv
  have hc : q • algebraMap ℝ (Matrix ι ι 𝕂) v =
      algebraMap ℝ (Matrix ι ι 𝕂) (q*v) := by
    rw [Algebra.smul_def, ← map_mul]
  have hqD : q • D ≤ algebraMap ℝ (Matrix ι ι 𝕂) (q*v) := by
    rw [← hc]
    exact smul_le_smul_of_nonneg_left hbound hq
  have hle : s • Y-algebraMap ℝ (Matrix ι ι 𝕂) (q*v) ≤ s • Y-q • D :=
    sub_le_sub_left hqD _
  have hleft : (s • Y-algebraMap ℝ (Matrix ι ι 𝕂) (q*v)).IsHermitian := by
    exact (hY.smul (show IsSelfAdjoint s from rfl)).sub
      (show IsSelfAdjoint (algebraMap ℝ (Matrix ι ι 𝕂) (q*v)) from
        (show IsSelfAdjoint (q*v) from rfl).algebraMap (Matrix ι ι 𝕂))
  have hright := (hY.smul (show IsSelfAdjoint s from rfl)).sub
    (hD.smul (show IsSelfAdjoint q from rfl))
  obtain ⟨r, hr, hrl⟩ := matrix_spectral_order hleft hright hle (matrix_affine_spectrum hY s (q*v) hl)
  exact ⟨r, hr, (sub_le_sub_right (mul_le_mul_of_nonneg_left htl hs) _).trans hrl⟩

#print axioms matrix_affine_spectrum
#print axioms matrix_variance_compensation
end SpectralRadiusUpperTail
