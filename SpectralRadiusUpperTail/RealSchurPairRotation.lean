import SpectralRadiusUpperTail.RealSchurPairOrbitJacobian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Standard one-parameter orthogonal rotations in dimension two. -/
noncomputable def realSchurRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem realSchurRotation_zero : realSchurRotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSchurRotation]

/-- The genuine rotation path has the generator used above as its
entrywise derivative at angle zero. -/
theorem realSchurRotation_hasDerivAt_zero (i j : Fin 2) :
    HasDerivAt (fun θ : ℝ => realSchurRotation θ i j)
      (realSchurRotationGenerator i j) 0 := by
  fin_cases i <;> fin_cases j
  · simpa [realSchurRotation, realSchurRotationGenerator]
      using Real.hasDerivAt_cos (0 : ℝ)
  · convert (Real.hasDerivAt_sin (0 : ℝ)).neg using 1 <;> try rfl
    all_goals simp [realSchurRotation, realSchurRotationGenerator]
  · simpa [realSchurRotation, realSchurRotationGenerator]
      using Real.hasDerivAt_sin (0 : ℝ)
  · simpa [realSchurRotation, realSchurRotationGenerator]
      using Real.hasDerivAt_cos (0 : ℝ)

/-- Closed form for the orthogonal orbit of a real Schur pair block. -/
noncomputable def realSchurRotatedBlock
    (θ x b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x+(c-b)*Real.sin θ*Real.cos θ,
      b*(Real.cos θ)^2+c*(Real.sin θ)^2;
      -(c*(Real.cos θ)^2+b*(Real.sin θ)^2),
      x+(b-c)*Real.sin θ*Real.cos θ]

theorem realSchurRotation_conjugate_block (θ x b c : ℝ) :
    realSchurRotation θ * realSchurBlock x b c *
      (realSchurRotation θ)ᵀ = realSchurRotatedBlock θ x b c := by
  have htrig := Real.sin_sq_add_cos_sq θ
  have hx : x*(Real.sin θ^2+Real.cos θ^2) = x := by rw [htrig]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSchurRotation, realSchurBlock, realSchurRotatedBlock,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [hx]

#print axioms realSchurRotation_zero
#print axioms realSchurRotation_hasDerivAt_zero
#print axioms realSchurRotation_conjugate_block
end SpectralRadiusUpperTail
