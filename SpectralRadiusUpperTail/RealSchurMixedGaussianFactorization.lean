import SpectralRadiusUpperTail.RealSchurMixedDiagonalDependence
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Squared-entry energy in the diagonal blocks. -/
def realSchurMixedDiagonalEnergy
    {m : ℕ} (s : Fin m → ℕ)
    (S : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) : ℝ :=
  ∑ p : RealSchurMixedCoord s × RealSchurMixedCoord s,
    if p.1.1 = p.2.1 then (S p.1 p.2)^2 else 0

/-- Squared-entry energy in the strictly upper blocks. -/
def realSchurMixedStrictUpperEnergy
    {m : ℕ} (s : Fin m → ℕ)
    (S : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) : ℝ :=
  ∑ p : RealSchurMixedCoord s × RealSchurMixedCoord s,
    if p.1.1 < p.2.1 then (S p.1 p.2)^2 else 0

theorem realSchurMixed_sum_squares_split
    {m : ℕ} (s : Fin m → ℕ)
    (S : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hS : realSchurMixedLowerProjection s S = 0) :
    (∑ p : RealSchurMixedCoord s × RealSchurMixedCoord s,
      (S p.1 p.2)^2) =
      realSchurMixedDiagonalEnergy s S +
        realSchurMixedStrictUpperEnergy s S := by
  unfold realSchurMixedDiagonalEnergy realSchurMixedStrictUpperEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hd : p.1.1=p.2.1
  · simp [hd]
  by_cases hu : p.1.1<p.2.1
  · simp [hd, hu]
  have hl : p.2.1<p.1.1 := by omega
  have hz : S p.1 p.2=0 :=
    (realSchurMixed_blockTriangular_iff_lower_zero s S).mpr hS
      (i := p.1) (j := p.2) hl
  simp [hd, hu, hz]

/-- On a block-upper matrix, the Gaussian density factors exactly into
diagonal-block and independent strictly-upper-block energies. -/
theorem realSchurMixedGaussianWeight_factor
    {m : ℕ} (s : Fin m → ℕ)
    (S : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hS : realSchurMixedLowerProjection s S = 0) :
    realMatrixGaussianWeight (RealSchurMixedCoord s) S =
      Real.exp (-realSchurMixedDiagonalEnergy s S/2) *
        Real.exp (-realSchurMixedStrictUpperEnergy s S/2) := by
  unfold realMatrixGaussianWeight
  rw [realSchurMixed_sum_squares_split s S hS, ← Real.exp_add]
  congr 1
  ring

/-- The local Gaussian Schur integrand separates its angular,
diagonal-block, and strictly-upper-block factors pointwise. -/
theorem realSchurMixedGaussianJacobian_factor
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (x : RealSchurMixedTangent s) :
    realSchurMixedJacobianWeight s T x *
        realMatrixGaussianWeight (RealSchurMixedCoord s) (T+x.2.val) =
      |realSchurMixedAngularJacobian s x.1| *
        ((∏ p : RealSchurLowerIndex m,
          |(realSchurMixedSylvester s (T+x.2.val) p).det|) *
          Real.exp (-realSchurMixedDiagonalEnergy s (T+x.2.val)/2)) *
        Real.exp (-realSchurMixedStrictUpperEnergy s (T+x.2.val)/2) := by
  have hx : realSchurMixedLowerProjection s x.2.val = 0 := x.2.property
  have hS : realSchurMixedLowerProjection s (T+x.2.val) = 0 := by
    rw [map_add, hT, hx, add_zero]
  rw [realSchurMixedGaussianWeight_factor s (T+x.2.val) hS]
  unfold realSchurMixedJacobianWeight
  ring

#print axioms realSchurMixed_sum_squares_split
#print axioms realSchurMixedGaussianWeight_factor
#print axioms realSchurMixedGaussianJacobian_factor
end SpectralRadiusUpperTail
