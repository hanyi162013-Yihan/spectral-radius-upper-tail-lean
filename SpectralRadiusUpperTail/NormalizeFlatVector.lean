import SpectralRadiusUpperTail.FlatUnitDirections
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

lemma normalize_coordinate_flat_bound (g : EuclideanSpace 𝕂 (Fin n))
    (hn : 0 < n) (K : ℝ) (hK : 0 ≤ K)
    (henergy : (n : ℝ)/4 ≤ ‖g‖^2) (hcoord : ∀ i, ‖g i‖ ≤ K) (i : Fin n) :
    ‖(‖g‖⁻¹ • g) i‖ ≤ (2*K)/Real.sqrt (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnorm : 0 < ‖g‖ := by nlinarith [norm_nonneg g]
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hs2 := Real.sq_sqrt hnpos.le
  have hlo : Real.sqrt (n : ℝ)/2 ≤ ‖g‖ := by nlinarith [norm_nonneg g]
  have he : ‖(‖g‖⁻¹ • g) i‖ = ‖g i‖/‖g‖ := by
    change ‖(‖g‖⁻¹ : ℝ) • g i‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hnorm.le)]
    ring
  rw [he,div_le_iff₀ hnorm]
  have hh := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (2*K)/Real.sqrt (n : ℝ) by positivity)
  have hc : (2*K)/Real.sqrt (n : ℝ)*(Real.sqrt (n : ℝ)/2) = K := by
    field_simp
  rw [hc] at hh
  exact (hcoord i).trans hh

lemma normalize_mem_flatUnitDirections (g : EuclideanSpace 𝕂 (Fin n))
    (hn : 0 < n) (K : ℝ) (hK : 0 ≤ K)
    (henergy : (n : ℝ)/4 ≤ ‖g‖^2) (hcoord : ∀ i, ‖g i‖ ≤ K) :
    (fun i => (‖g‖⁻¹ • g) i) ∈ flatUnitDirections 𝕂 n (2*K) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnorm : 0 < ‖g‖ := by nlinarith [norm_nonneg g]
  have hunit : (∑ i, ‖(‖g‖⁻¹ • g) i‖^2) = 1 := by
    rw [← EuclideanSpace.norm_sq_eq,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hnorm.le),inv_mul_cancel₀ (ne_of_gt hnorm),one_pow]
  exact ⟨hunit.le,fun _ => hunit,normalize_coordinate_flat_bound g hn K hK henergy hcoord⟩

#print axioms normalize_coordinate_flat_bound
#print axioms normalize_mem_flatUnitDirections
end SpectralRadiusUpperTail
