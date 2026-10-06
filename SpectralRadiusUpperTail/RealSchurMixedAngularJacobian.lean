import SpectralRadiusUpperTail.RealSchurMixedMovingDeterminant
import Ginibre.ExpAngularConjugation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- The actual moving-frame angular derivative of the matrix exponential. -/
noncomputable def realSchurMixedMaurerCartan
    {m : ℕ} (s : Fin m → ℕ)
    (w : RealSchurMixedOrbitIndex s → ℝ) :
    (RealSchurMixedOrbitIndex s → ℝ) →ₗ[ℝ]
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ where
  toFun v := NormedSpace.exp (-realSchurMixedSkewCLM s w) *
    fderiv ℝ (fun u => NormedSpace.exp (realSchurMixedSkewCLM s u)) w v
  map_add' v u := by rw [map_add, Matrix.mul_add]
  map_smul' a v := by rw [map_smul, Matrix.mul_smul]; rfl

/-- The angular factor is defined entirely from the angular exponential;
it contains no block-upper matrix parameter. -/
noncomputable def realSchurMixedAngularJacobian
    {m : ℕ} (s : Fin m → ℕ)
    (w : RealSchurMixedOrbitIndex s → ℝ) : ℝ :=
  LinearMap.det ((-(realSchurMixedLowerProjection s).toLinearMap).comp
    (realSchurMixedMaurerCartan s w))

/-- Derivative of the genuine real-Schur exponential chart, rotated into
the moving orthogonal frame at an arbitrary parameter. -/
theorem realSchurMixedExpCoordinates_fderiv_rotated
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x v : RealSchurMixedTangent s) :
    (realSchurMixedAngularFrame s x.1)ᵀ *
      fderiv ℝ (realSchurMixedExpCoordinates s T) x v *
        realSchurMixedAngularFrame s x.1 =
      realSchurMixedMovingTangentMap s (T+x.2.val)
        (realSchurMixedMaurerCartan s x.1) v := by
  have hskew : ((realSchurMixedSkewCLM s) x.1)ᵀ =
      -((realSchurMixedSkewCLM s) x.1) :=
    realSchurMixedSkewEmbed_transpose s x.1
  rw [realSchurMixedAngularFrame, ← Matrix.exp_transpose, hskew]
  convert! Ginibre.fderiv_exp_angular_conjugation_rotated T
    (realSchurMixedSkewCLM s)
    ((realSchurMixedUpperTangentCLM s).comp
      (ContinuousLinearMap.inr ℝ _ _)) x v using 1

theorem realSchurMixedMaurerCartan_zero
    {m : ℕ} (s : Fin m → ℕ)
    (v : RealSchurMixedOrbitIndex s → ℝ) :
    realSchurMixedMaurerCartan s 0 v = realSchurMixedSkewEmbed s v := by
  change NormedSpace.exp (-realSchurMixedSkewCLM s 0) *
    fderiv ℝ (fun u => NormedSpace.exp (realSchurMixedSkewCLM s u)) 0 v = _
  have he : HasFDerivAt
      (fun u => NormedSpace.exp (realSchurMixedSkewCLM s u))
      (realSchurMixedSkewCLM s) 0 := by
    convert! (Ginibre.hasStrictFDerivAt_exp_linear
      (realSchurMixedSkewCLM s)).hasFDerivAt
  rw [he.fderiv]
  simp only [map_zero, neg_zero, NormedSpace.exp_zero, one_mul]
  rfl

/-- The angular factor is normalized to one at the chart center. -/
theorem realSchurMixedAngularJacobian_zero
    {m : ℕ} (s : Fin m → ℕ) :
    realSchurMixedAngularJacobian s 0 = 1 := by
  have he : (-(realSchurMixedLowerProjection s).toLinearMap).comp
      (realSchurMixedMaurerCartan s 0) =
      (LinearMap.id : (RealSchurMixedOrbitIndex s → ℝ) →ₗ[ℝ]
        (RealSchurMixedOrbitIndex s → ℝ)) := by
    apply LinearMap.ext
    intro v
    change -realSchurMixedLowerProjection s
      (realSchurMixedMaurerCartan s 0 v) = v
    rw [realSchurMixedMaurerCartan_zero,
      realSchurMixedLowerProjection_skewEmbed, neg_neg]
  change LinearMap.det _ = 1
  rw [he, LinearMap.det_id]

#print axioms realSchurMixedExpCoordinates_fderiv_rotated
#print axioms realSchurMixedAngularJacobian_zero
end SpectralRadiusUpperTail
