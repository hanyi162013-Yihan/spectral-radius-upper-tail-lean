import SpectralRadiusUpperTail.ConcreteTriangular

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.Frobenius
open Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

/-- The regression equations need only hold at the actual finite coordinates.
Zero extension supplies the previously checked infinite-sequence interface. -/
theorem finite_tail_regression_row (η : ℝ) (hη : 0 < η)
    (v x z e r : Fin N → 𝕂) (t : 𝕂)
    (hx : ∀ j : Fin N, x j = z j +
      (star (v j)/(tailDenominator η v j.val : 𝕂))*
        (t-weightedPrefix (zeroExtendVector v) (zeroExtendVector x) j.val) + e j + r j) :
    x = (fun i => z i+e i+r i) ᵥ*
      triangularInverseMatrix N (zeroExtendVector v) (fun j => star (zeroExtendVector v j))
        (fun j => (tailDenominator η v j : 𝕂)) +
      (fun i => t*(star (v i)/((η+∑ k, ‖v k‖^2 : ℝ) : 𝕂))) := by
  have hall (j : ℕ) : zeroExtendVector x j = zeroExtendVector z j +
      (star (zeroExtendVector v j)/(tailDenominator η v j : 𝕂))*
        (t-weightedPrefix (zeroExtendVector v) (zeroExtendVector x) j) +
      zeroExtendVector e j + zeroExtendVector r j := by
    by_cases hj : j < N
    · simpa only [zeroExtendVector, dif_pos hj] using hx ⟨j,hj⟩
    · simp [zeroExtendVector, hj]
  have hh := triangular_regression_row (zeroExtendVector v)
    (fun j => star (zeroExtendVector v j)) (fun j => (tailDenominator η v j : 𝕂))
    (zeroExtendVector x) (zeroExtendVector z) (zeroExtendVector e) (zeroExtendVector r) t
    (tailDenominator_cast_ne_zero η hη v) (tailDenominator_cast_sub η v) hall N
  simpa only [zeroExtendVector_fin, tailDenominator_zero] using hh

#print axioms finite_tail_regression_row
end SpectralRadiusUpperTail
