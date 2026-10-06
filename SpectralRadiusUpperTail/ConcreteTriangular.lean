import SpectralRadiusUpperTail.TailDenominator

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.Frobenius
open Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

lemma tail_triangular_inverse_sub_one (a : ℝ) (v : Fin n → 𝕂) :
    triangularInverseMatrix n (zeroExtendVector v) (fun j => star (zeroExtendVector v j))
      (fun j => (tailDenominator a v j : 𝕂)) - 1 =
      triangularCorrection v (fun i => tailDenominator a v (i.val+1)) := by
  ext i j
  simp only [triangularInverseMatrix, Matrix.sub_apply, Matrix.of_apply,
    zeroExtendVector_fin, triangularCorrection]
  by_cases hij : i < j
  · simp only [hij, if_true]
    ring
  · simp [hij]

theorem tail_triangular_inverse_norm_sq_le (a : ℝ) (ha : 0 < a)
    (v : Fin n → 𝕂) (hv : ∑ i, ‖v i‖^2 = 1) :
    ‖triangularInverseMatrix n (zeroExtendVector v) (fun j => star (zeroExtendVector v j))
      (fun j => (tailDenominator a v j : 𝕂)) - 1‖^2 ≤ 1/(2*a^2) := by
  rw [tail_triangular_inverse_sub_one]
  exact tail_triangularCorrection_norm_sq_le a ha v hv

theorem tail_triangular_mean (a : ℝ) (ha : 0 < a)
    (v : Fin n → 𝕂) (hv : ∑ i, ‖v i‖^2 = 1) :
    (fun i : Fin n => star (v i) / (tailDenominator a v i : 𝕂)) ᵥ*
      triangularInverseMatrix n (zeroExtendVector v) (fun j => star (zeroExtendVector v j))
        (fun j => (tailDenominator a v j : 𝕂)) =
      fun i : Fin n => star (v i) / ((a+1 : ℝ) : 𝕂) := by
  have h := triangular_mean_vecMul (zeroExtendVector v)
    (fun j => star (zeroExtendVector v j)) (fun j => (tailDenominator a v j : 𝕂))
    (tailDenominator_cast_ne_zero a ha v) (tailDenominator_cast_sub a v) n
  simpa only [zeroExtendVector_fin, tailDenominator_zero, hv] using h

/-- Pointwise regression equations give the exact transformed row identity.
The probabilistic estimates on the error rows are separate hypotheses elsewhere. -/
theorem triangular_regression_row (v u d x z e r : ℕ → 𝕂) (t : 𝕂)
    (hd : ∀ j, d j ≠ 0) (hdu : ∀ j, d j-d (j+1)=v j*u j)
    (hx : ∀ j, x j = z j + (u j/d j)*(t-weightedPrefix v x j) + e j + r j)
    (n : ℕ) :
    (fun i : Fin n => x i) =
      (fun i : Fin n => z i + e i + r i) ᵥ* triangularInverseMatrix n v u d +
        (fun i : Fin n => t * (u i / d 0)) := by
  have hf : (fun i : Fin n => x i) ᵥ* triangularForwardMatrix n v u d =
      (fun i : Fin n => z i + e i + r i) + (fun i : Fin n => t*(u i/d i)) := by
    funext j
    rw [vecMul_triangularForwardMatrix]
    unfold triangularForward
    rw [hx j]
    simp only [Pi.add_apply]
    ring
  have hm := congrArg (fun w : Fin n → 𝕂 => w ᵥ* triangularInverseMatrix n v u d) hf
  rw [vecMul_vecMul, triangular_matrices_mul v u d hd hdu n, vecMul_one,
    add_vecMul] at hm
  have ht : (fun i : Fin n => t*(u i/d i)) ᵥ* triangularInverseMatrix n v u d =
      fun i : Fin n => t*(u i/d 0) := by
    change (t • (fun i : Fin n => u i/d i)) ᵥ* triangularInverseMatrix n v u d = _
    rw [smul_vecMul, triangular_mean_vecMul v u d hd hdu n]
    rfl
  rw [ht] at hm
  exact hm

#print axioms tail_triangular_inverse_norm_sq_le
#print axioms triangular_regression_row
end SpectralRadiusUpperTail
