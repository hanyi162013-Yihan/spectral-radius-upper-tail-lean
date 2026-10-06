import SpectralRadiusUpperTail.RealSchurMixedGaussianFiber
import SpectralRadiusUpperTail.RealSchurMixedBlockScalar
import SpectralRadiusUpperTail.RealSchurMixedAngularPositive

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator BigOperators

noncomputable def realSchurMixedDiagonalGaussianJacobian
    {m : ℕ} (s : Fin m → ℕ) (d : RealSchurMixedDiagonalEntry s → ℝ) : ℝ :=
  (∏ p : RealSchurLowerIndex m,
    |(realSchurMixedSylvester s (realSchurMixedUpperEntryJoin s d 0) p).det|) *
      Real.exp (-(∑ p : RealSchurMixedDiagonalEntry s, (d p)^2)/2)

theorem realSchurMixedDiagonalGaussianJacobian_nonneg
    {m : ℕ} (s : Fin m → ℕ) (d : RealSchurMixedDiagonalEntry s → ℝ) :
    0 ≤ realSchurMixedDiagonalGaussianJacobian s d :=
  mul_nonneg (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) (Real.exp_pos _).le

theorem realSchurMixedDiagonalGaussianJacobian_continuous
    {m : ℕ} (s : Fin m → ℕ) :
    Continuous (realSchurMixedDiagonalGaussianJacobian s) := by
  have hSylv (p : RealSchurLowerIndex m) : Continuous
      (fun d : RealSchurMixedDiagonalEntry s → ℝ =>
        realSchurMixedSylvester s (realSchurMixedUpperEntryJoin s d 0) p) := by
    apply continuous_matrix
    intro i j
    unfold realSchurMixedSylvester realSchurMixedUpperEntryJoin
    split_ifs <;> fun_prop
  unfold realSchurMixedDiagonalGaussianJacobian
  apply Continuous.mul
  · exact continuous_finset_prod _ (fun p _ => (hSylv p).matrix_det.abs)
  · fun_prop

/-- A regular scalar-block marker supplies continuity of the angular
Jacobian for every positive block shape, independently of sampled data. -/
theorem realSchurMixedAngularJacobian_continuous_of_shape
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c) :
    Continuous (realSchurMixedAngularJacobian s) :=
  realSchurMixedAngularJacobian_continuous s (realSchurMixedBlockScalar s c)
    (realSchurMixedBlockScalar_lower_zero s c)
    (realSchurMixedBlockScalar_orbit_det_ne_zero s hs c hc)

/-- The actual Jacobian times Gaussian density has one angular factor,
one diagonal-block factor, and a standard Gaussian strict-upper factor. -/
theorem realSchurMixedFlagGaussian_fiber_factor
    {m : ℕ} (s : Fin m → ℕ) (w : RealSchurMixedOrbitIndex s → ℝ)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    realSchurMixedJacobianWeight s 0 (realSchurMixedFiberPoint s w d u) *
      realMatrixGaussianWeight (RealSchurMixedCoord s) (realSchurMixedUpperEntryJoin s d u) =
      |realSchurMixedAngularJacobian s w| *
        (realSchurMixedDiagonalGaussianJacobian s d *
          Real.exp (-(∑ p : RealSchurMixedStrictUpperEntry s, (u p)^2)/2)) := by
  rw [realSchurMixedJacobianWeight_fiber_const s w d u 0,
    realSchurMixedGaussianWeight_join]
  unfold realSchurMixedJacobianWeight realSchurMixedDiagonalGaussianJacobian
  simp only [zero_add, realSchurMixedFiberPoint_upper]
  change ((∏ p : RealSchurLowerIndex m,
    |(realSchurMixedSylvester s (realSchurMixedUpperEntryJoin s d 0) p).det|) *
      |realSchurMixedAngularJacobian s w|) * _ = _
  ring

#print axioms realSchurMixedDiagonalGaussianJacobian_nonneg
#print axioms realSchurMixedDiagonalGaussianJacobian_continuous
#print axioms realSchurMixedAngularJacobian_continuous_of_shape
#print axioms realSchurMixedFlagGaussian_fiber_factor
end SpectralRadiusUpperTail
