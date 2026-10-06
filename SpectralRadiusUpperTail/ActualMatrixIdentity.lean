import SpectralRadiusUpperTail.ActualRegressionIdentity
import SpectralRadiusUpperTail.ReversedMatrix
import SpectralRadiusUpperTail.GaussianRegressionMatrix

namespace SpectralRadiusUpperTail
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- The actual pointwise row identity in the original coordinate order. -/
theorem gaussianRow_triangular_identity (μ : Measure 𝕂) (a : ℝ) (v : ℕ → 𝕂)
    (t : 𝕂) (η : ℝ) (hη : 0 < η) (x z : Fin N → 𝕂) :
    x = (fun j => z j+gaussianRowCenteredIncrement μ a v j t x z+
      gaussianRowRegression μ a v j t η x) ᵥ*
        descendingTriangularInverse η (fun j : Fin N => v j.val) +
      (fun j => t*(star (v j.val)/((η+∑ k : Fin N, ‖v k.val‖^2 : ℝ) : 𝕂))) := by
  funext j
  have hh := congrFun (gaussianRow_reversed_triangular_identity μ a v t η hη x z) j.rev
  rw [Pi.add_apply, Fin.rev_rev] at hh
  change x j = _
  simpa only [descendingTriangularInverse, Pi.add_apply, vecMul_reverseMatrix] using hh

noncomputable def normalizedArray (x : Fin N → Fin N → 𝕂) : Matrix (Fin N) (Fin N) 𝕂 :=
  fun i j => (1/Real.sqrt (N : ℝ) : ℝ) • x i j

noncomputable def gaussianCenteredMatrix (μ : Measure 𝕂) (a : ℝ) (v : ℕ → 𝕂)
    (t : Fin N → 𝕂) (x z : Fin N → Fin N → 𝕂) : Matrix (Fin N) (Fin N) 𝕂 :=
  fun i j => (1/Real.sqrt (N : ℝ) : ℝ) • gaussianRowCenteredIncrement μ a v j (t i) (x i) (z i)

noncomputable def gaussianMeanMatrix (v : ℕ → 𝕂) (t : Fin N → 𝕂) (η : ℝ) :
    Matrix (Fin N) (Fin N) 𝕂 :=
  fun i j => (1/Real.sqrt (N : ℝ) : ℝ) •
    (t i*(star (v j.val)/((η+∑ k : Fin N, ‖v k.val‖^2 : ℝ) : 𝕂)))

/-- Complete normalized matrix equality with the actual conditional centered
increments and the same actual regression matrix whose probability limit is proved. -/
theorem gaussianMatrix_triangular_identity (μ : Measure 𝕂) (a : ℝ) (v : ℕ → 𝕂)
    (t : Fin N → 𝕂) (η : ℝ) (hη : 0 < η) (x z : Fin N → Fin N → 𝕂) :
    normalizedArray x =
      (normalizedArray z+gaussianCenteredMatrix μ a v t x z+gaussianRegressionMatrix μ a v t η x)*
        descendingTriangularInverse η (fun j : Fin N => v j.val)+gaussianMeanMatrix v t η := by
  ext i j
  have hh := congrFun (gaussianRow_triangular_identity μ a v (t i) η hη (x i) (z i)) j
  have hs := congrArg (fun w : 𝕂 => (1/Real.sqrt (N : ℝ) : ℝ) • w) hh
  simpa only [normalizedArray, gaussianCenteredMatrix, gaussianRegressionMatrix,
    gaussianMeanMatrix, Matrix.add_apply, Matrix.mul_apply, vecMul, dotProduct,
    Pi.add_apply, smul_add, Finset.smul_sum, ← smul_mul_assoc] using hs

#print axioms gaussianRow_triangular_identity
#print axioms gaussianMatrix_triangular_identity
end SpectralRadiusUpperTail
