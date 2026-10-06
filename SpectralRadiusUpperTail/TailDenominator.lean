import SpectralRadiusUpperTail.TriangularMatrix
import SpectralRadiusUpperTail.TriangularNorm

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

def zeroExtendVector (v : Fin n → 𝕂) (j : ℕ) : 𝕂 :=
  if h : j < n then v ⟨j,h⟩ else 0

lemma zeroExtendVector_fin (v : Fin n → 𝕂) (i : Fin n) :
    zeroExtendVector v i = v i := by simp [zeroExtendVector, i.isLt]

def tailDenominator (a : ℝ) (v : Fin n → 𝕂) (j : ℕ) : ℝ :=
  a + ∑ i : Fin n, if j ≤ i.val then ‖v i‖^2 else 0

lemma tailDenominator_ge (a : ℝ) (v : Fin n → 𝕂) (j : ℕ) :
    a ≤ tailDenominator a v j := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)

lemma tailDenominator_zero (a : ℝ) (v : Fin n → 𝕂) :
    tailDenominator a v 0 = a + ∑ i, ‖v i‖^2 := by simp [tailDenominator]

lemma tailDenominator_sub (a : ℝ) (v : Fin n → 𝕂) (j : ℕ) :
    tailDenominator a v j - tailDenominator a v (j+1) = ‖zeroExtendVector v j‖^2 := by
  have hsum : (∑ i : Fin n, if j ≤ i.val then ‖v i‖^2 else 0) -
      (∑ i : Fin n, if j+1 ≤ i.val then ‖v i‖^2 else 0) =
        ∑ i : Fin n, if j = i.val then ‖v i‖^2 else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hji : j = i.val
    · subst j; simp
    · have hiff : j ≤ i.val ↔ j+1 ≤ i.val := by omega
      by_cases hle : j ≤ i.val
      · simp [hle, hiff.mp hle, hji]
      · simp [hle, not_iff_not.mpr hiff |>.mp hle, hji]
  have hcancel : tailDenominator a v j - tailDenominator a v (j+1) =
      ∑ i : Fin n, if j = i.val then ‖v i‖^2 else 0 := by
    unfold tailDenominator
    simpa only [add_sub_add_left_eq_sub] using hsum
  rw [hcancel]
  by_cases hj : j < n
  · rw [Finset.sum_eq_single (⟨j,hj⟩ : Fin n)]
    · simp [zeroExtendVector, hj]
    · intro i _ hi
      have hji : j ≠ i.val := by
        intro h
        apply hi
        exact Fin.ext h.symm
      simp [hji]
    · simp
  · have hz : ∀ i : Fin n, j ≠ i.val := by intro i h; exact hj (h ▸ i.isLt)
    simp [zeroExtendVector, hj, hz]

lemma tailDenominator_cast_ne_zero (a : ℝ) (ha : 0 < a) (v : Fin n → 𝕂) (j : ℕ) :
    (tailDenominator a v j : 𝕂) ≠ 0 := by
  exact_mod_cast ne_of_gt (lt_of_lt_of_le ha (tailDenominator_ge a v j))

lemma tailDenominator_cast_sub (a : ℝ) (v : Fin n → 𝕂) (j : ℕ) :
    (tailDenominator a v j : 𝕂) - (tailDenominator a v (j+1) : 𝕂) =
      zeroExtendVector v j * star (zeroExtendVector v j) := by
  rw [← RCLike.ofReal_sub, tailDenominator_sub, RCLike.ofReal_pow]
  exact (RCLike.mul_conj (zeroExtendVector v j)).symm

/-- The concrete tail sums satisfy all hypotheses of the exact triangular inverse. -/
theorem tail_triangular_inverse (a : ℝ) (ha : 0 < a) (v : Fin n → 𝕂) :
    triangularForwardMatrix n (zeroExtendVector v) (fun j => star (zeroExtendVector v j))
      (fun j => (tailDenominator a v j : 𝕂)) *
    triangularInverseMatrix n (zeroExtendVector v) (fun j => star (zeroExtendVector v j))
      (fun j => (tailDenominator a v j : 𝕂)) = 1 :=
  triangular_matrices_mul _ _ _ (tailDenominator_cast_ne_zero a ha v)
    (tailDenominator_cast_sub a v) n

theorem tail_triangularCorrection_norm_sq_le (a : ℝ) (ha : 0 < a)
    (v : Fin n → 𝕂) (hv : ∑ i, ‖v i‖^2 = 1) :
    ‖triangularCorrection v (fun i => tailDenominator a v (i.val+1))‖^2 ≤ 1/(2*a^2) :=
  triangularCorrection_norm_sq_le v _ a ha (fun i => tailDenominator_ge a v (i.val+1)) hv

#print axioms tail_triangular_inverse
#print axioms tail_triangularCorrection_norm_sq_le
end SpectralRadiusUpperTail
