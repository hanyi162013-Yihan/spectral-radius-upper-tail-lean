import SpectralRadiusUpperTail.RealSchurMixedOutputRotation
import Ginibre.SchurSmooth
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator ContDiff

/-- Smoothness of the genuine mixed real-Schur chart on its full
parameter space. -/
theorem realSchurMixedExpCoordinates_contDiff
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (k : ℕ∞ω) :
    ContDiff ℝ k (realSchurMixedExpCoordinates s T) := by
  convert! Ginibre.contDiff_exp_conjugation k T
    (realSchurMixedSkewTangentCLM s)
    (realSchurMixedUpperTangentCLM s)

/-- The real-linear map induced on fixed entry coordinates by
two-sided multiplication. -/
noncomputable def realSchurMixedEntryConjugation
    {m : ℕ} (s : Fin m → ℕ)
    (A B : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    RealSchurMixedTangent s →ₗ[ℝ] RealSchurMixedTangent s :=
  (realSchurMixedEntryEquiv s).toLinearMap.comp
    ((realMatrixTwoSidedMul (RealSchurMixedCoord s) A B).comp
      (realSchurMixedEntryEquiv s).symm.toLinearMap)

theorem realSchurMixedEntryConjugation_det_of_inverse
    {m : ℕ} (s : Fin m → ℕ)
    (A B : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hAB : A*B=1) :
    LinearMap.det (realSchurMixedEntryConjugation s A B) = 1 := by
  change LinearMap.det ((realSchurMixedEntryEquiv s).toLinearMap.comp
    ((realMatrixTwoSidedMul (RealSchurMixedCoord s) A B).comp
      (realSchurMixedEntryEquiv s).symm.toLinearMap)) = 1
  rw [LinearMap.det_conj]
  exact realMatrixTwoSidedMul_det_of_inverse (RealSchurMixedCoord s) A B hAB

theorem realSchurMixedEntryCoordinates_fderiv_apply
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x v : RealSchurMixedTangent s) :
    fderiv ℝ (realSchurMixedEntryCoordinates s T) x v =
      realSchurMixedEntryEquiv s
        (fderiv ℝ (realSchurMixedExpCoordinates s T) x v) := by
  have hf := ((realSchurMixedExpCoordinates_contDiff s T 1).differentiable
    (by simp)) x
  have h : HasFDerivAt (realSchurMixedEntryCoordinates s T)
      ((realSchurMixedEntryEquiv s).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (realSchurMixedExpCoordinates s T) x)) x := by
    convert! (realSchurMixedEntryEquiv s).toContinuousLinearEquiv.hasFDerivAt.comp
      x hf.hasFDerivAt
  rw [h.fderiv]
  rfl

theorem realSchurMixedRotatedDifferential_eq_output_comp
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x : RealSchurMixedTangent s) :
    realSchurMixedRotatedDifferential s T x =
      (realSchurMixedEntryConjugation s
        (realSchurMixedAngularFrame s x.1)ᵀ
        (realSchurMixedAngularFrame s x.1)).comp
          (fderiv ℝ (realSchurMixedEntryCoordinates s T) x).toLinearMap := by
  apply LinearMap.ext
  intro v
  change realSchurMixedEntryEquiv s
    ((realSchurMixedAngularFrame s x.1)ᵀ *
      fderiv ℝ (realSchurMixedExpCoordinates s T) x v *
        realSchurMixedAngularFrame s x.1) =
    realSchurMixedEntryEquiv s
      ((realSchurMixedAngularFrame s x.1)ᵀ *
        (realSchurMixedEntryEquiv s).symm
          (fderiv ℝ (realSchurMixedEntryCoordinates s T) x v) *
        realSchurMixedAngularFrame s x.1)
  rw [realSchurMixedEntryCoordinates_fderiv_apply,
    LinearEquiv.symm_apply_apply]

theorem realSchurMixedRotatedDifferential_det_eq
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x : RealSchurMixedTangent s) :
    LinearMap.det (realSchurMixedRotatedDifferential s T x) =
      (fderiv ℝ (realSchurMixedEntryCoordinates s T) x).det := by
  rw [realSchurMixedRotatedDifferential_eq_output_comp,
    LinearMap.det_comp,
    realSchurMixedEntryConjugation_det_of_inverse s _ _
      (realSchurMixedAngularFrame_orthogonal s x.1), one_mul]

/-- Full Jacobian of the actual mixed real-Schur coordinate map at every
parameter point. Its angular factor is independent of the matrix blocks. -/
theorem realSchurMixedEntryCoordinates_fderiv_det_everywhere
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (x : RealSchurMixedTangent s) :
    (fderiv ℝ (realSchurMixedEntryCoordinates s T) x).det =
      (realSchurMixedOrbitMatrix s (T+x.2.val)).det *
        realSchurMixedAngularJacobian s x.1 := by
  rw [← realSchurMixedRotatedDifferential_det_eq]
  exact realSchurMixedRotatedDifferential_det s T hT x

/-- Nonnegative Jacobian weight for local change of variables. -/
theorem realSchurMixedEntryCoordinates_fderiv_abs_det_everywhere
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (x : RealSchurMixedTangent s) :
    |(fderiv ℝ (realSchurMixedEntryCoordinates s T) x).det| =
      (∏ p : RealSchurLowerIndex m,
        |(realSchurMixedSylvester s (T+x.2.val) p).det|) *
        |realSchurMixedAngularJacobian s x.1| := by
  rw [realSchurMixedEntryCoordinates_fderiv_det_everywhere s T hT x,
    abs_mul]
  congr 1
  have hupper : realSchurMixedLowerProjection s (T+x.2.val) = 0 := by
    have hx : realSchurMixedLowerProjection s x.2.val = 0 := x.2.property
    rw [map_add, hT, hx, add_zero]
  rw [realSchurMixedOrbitMatrix_det s hs (T+x.2.val)]
  · rw [Finset.abs_prod]
  · intro a b hba u v
    exact (realSchurMixed_blockTriangular_iff_lower_zero s _).mpr hupper
      (i := ⟨a,u⟩) (j := ⟨b,v⟩) hba

#print axioms realSchurMixedEntryCoordinates_fderiv_det_everywhere
#print axioms realSchurMixedEntryCoordinates_fderiv_abs_det_everywhere
end SpectralRadiusUpperTail
