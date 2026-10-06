import SpectralRadiusUpperTail.GaussianRowRegression
import SpectralRadiusUpperTail.FiniteTriangularRegression
import SpectralRadiusUpperTail.ReversedRow

namespace SpectralRadiusUpperTail
open MeasureTheory Matrix
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- Actual source-minus-comparator increment centered by the descending
conditional source mean. Its martingale properties require the sequential law. -/
noncomputable def gaussianRowCenteredIncrement (μ : Measure 𝕂) (a : ℝ) (v : ℕ → 𝕂)
    (j : Fin N) (t : 𝕂) (x z : Fin N → 𝕂) : 𝕂 :=
  x j-z j-(∫ y : 𝕂, y ∂gaussianEntryLaw μ a (fun i : Fin j.val => v i.val)
    (v j.val) (upperRowTarget v j t x))

lemma gaussianRow_regression_equation (μ : Measure 𝕂) (a : ℝ) (v : ℕ → 𝕂)
    (j : Fin N) (t : 𝕂) (η : ℝ) (x z : Fin N → 𝕂) :
    x j = z j +
      (star (v j.val)/((η+(∑ i : Fin j.val, ‖v i.val‖^2)+‖v j.val‖^2 : ℝ) : 𝕂))*
        upperRowTarget v j t x + gaussianRowCenteredIncrement μ a v j t x z +
        gaussianRowRegression μ a v j t η x := by
  simp only [gaussianRowCenteredIncrement, gaussianRowRegression,
    RCLike.real_smul_eq_coe_mul, RCLike.ofReal_div, RCLike.ofReal_one]
  ring

/-- Exact triangular identity for the actual conditional regression, after
reversing coordinates. The error rows are actual functions, not assumed proxies. -/
theorem gaussianRow_reversed_triangular_identity (μ : Measure 𝕂) (a : ℝ)
    (v : ℕ → 𝕂) (t : 𝕂) (η : ℝ) (hη : 0 < η) (x z : Fin N → 𝕂) :
    (fun i : Fin N => x i.rev) =
      (fun i : Fin N => z i.rev + gaussianRowCenteredIncrement μ a v i.rev t x z +
        gaussianRowRegression μ a v i.rev t η x) ᵥ*
      triangularInverseMatrix N (zeroExtendVector (fun i : Fin N => v i.rev.val))
        (fun j => star (zeroExtendVector (fun i : Fin N => v i.rev.val) j))
        (fun j => (tailDenominator η (fun i : Fin N => v i.rev.val) j : 𝕂)) +
      (fun i : Fin N => t*(star (v i.rev.val)/((η+∑ k : Fin N, ‖v k.val‖^2 : ℝ) : 𝕂))) := by
  have hx (j : Fin N) := gaussianRow_regression_equation μ a v j.rev t η x z
  have hh := finite_tail_regression_row η hη (fun i : Fin N => v i.rev.val)
    (fun i : Fin N => x i.rev) (fun i : Fin N => z i.rev)
    (fun i : Fin N => gaussianRowCenteredIncrement μ a v i.rev t x z)
    (fun i : Fin N => gaussianRowRegression μ a v i.rev t η x) t (fun j => ?_)
  · simpa only [sum_fin_reverse (fun k : Fin N => ‖v k.val‖^2)] using hh
  · have hden := tailDenominator_reverse η v j.rev
    simp only [Fin.rev_rev] at hden
    rw [hden]
    have hS := upperRowTarget_reverse v j.rev t x
    simp only [Fin.rev_rev] at hS
    rw [← hS]
    exact hx j

#print axioms gaussianRow_regression_equation
#print axioms gaussianRow_reversed_triangular_identity
end SpectralRadiusUpperTail
