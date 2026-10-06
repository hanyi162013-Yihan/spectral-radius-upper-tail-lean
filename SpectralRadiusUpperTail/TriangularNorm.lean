import SpectralRadiusUpperTail.TriangularEnergy
import Mathlib.Analysis.Matrix.Normed

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.Frobenius
variable {n : ℕ}

lemma ordered_pair_mass_le_half (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hnorm : ∑ i, w i = 1) :
    (∑ i, ∑ j, if i < j then w i * w j else 0) ≤ 1/2 := by
  have hp (i j : Fin n) :
      (if i < j then w i * w j else 0) +
        (if j < i then w i * w j else 0) ≤ w i * w j := by
    by_cases hij : i < j
    · simp [hij, not_lt_of_ge hij.le]
    · by_cases hji : j < i
      · simp [hij, hji]
      · simpa only [if_neg hij, if_neg hji, zero_add] using mul_nonneg (hw i) (hw j)
  have hswap : (∑ i, ∑ j, if j < i then w i * w j else 0) =
      ∑ i, ∑ j, if i < j then w i * w j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [mul_comm]
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ => Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun j _ => hp i j))
  simp only [Finset.sum_add_distrib] at hs
  rw [hswap, ← Finset.sum_mul_sum, hnorm] at hs
  linarith

lemma frobenius_norm_sq_eq_sum {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix (Fin n) (Fin n) 𝕜) : ‖A‖^2 = ∑ i, ∑ j, ‖A i j‖^2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · simp only [Real.rpow_two]
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) _))

/-- The strict upper triangular correction in the coupling, with d_i denoting
the already shifted denominator d_(i+1) from the manuscript. -/
def triangularCorrection {𝕜 : Type*} [RCLike 𝕜]
    (v : Fin n → 𝕜) (d : Fin n → ℝ) : Matrix (Fin n) (Fin n) 𝕜 :=
  fun i j => if i < j then -v i * star (v j) / (d i : 𝕜) else 0

/-- Actual Frobenius norm estimate, uniformly for real and complex matrices. -/
theorem triangularCorrection_norm_sq_le {𝕜 : Type*} [RCLike 𝕜]
    (v : Fin n → 𝕜) (d : Fin n → ℝ) (a : ℝ) (ha : 0 < a)
    (hd : ∀ i, a ≤ d i) (hv : ∑ i, ‖v i‖^2 = 1) :
    ‖triangularCorrection v d‖^2 ≤ 1/(2*a^2) := by
  have hentry (i j : Fin n) :
      ‖triangularCorrection v d i j‖^2 ≤
        (if i < j then ‖v i‖^2 * ‖v j‖^2 else 0) / a^2 := by
    by_cases hij : i < j
    · simp only [triangularCorrection, if_pos hij, norm_div, norm_mul,
        norm_neg, norm_star, RCLike.norm_ofReal, div_pow, mul_pow, sq_abs]
      apply div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (sq_pos_of_pos ha)
      have hi := hd i
      nlinarith
    · simp [triangularCorrection, hij]
  rw [frobenius_norm_sq_eq_sum]
  calc
    (∑ i, ∑ j, ‖triangularCorrection v d i j‖^2) ≤
        ∑ i, ∑ j, (if i < j then ‖v i‖^2 * ‖v j‖^2 else 0) / a^2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hentry i j))
    _ = (∑ i, ∑ j, if i < j then ‖v i‖^2 * ‖v j‖^2 else 0) / a^2 := by
      simp only [Finset.sum_div]
    _ ≤ (1/2)/a^2 := div_le_div_of_nonneg_right
      (ordered_pair_mass_le_half _ (fun i => sq_nonneg _) hv) (sq_nonneg a)
    _ = 1/(2*a^2) := by ring

#print axioms triangularCorrection_norm_sq_le
end SpectralRadiusUpperTail
