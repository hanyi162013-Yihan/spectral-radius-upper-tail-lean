import SpectralRadiusUpperTail.RealSchurMixedFlagFiberIntegration
import SpectralRadiusUpperTail.RealSchurMixedFlagGaussianFactors
import SpectralRadiusUpperTail.RealSchurMixedGaussianUpperLIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator BigOperators

/-- On one actual coded source, the whole strict-upper Gaussian array
integrates out with its exact normalizer. Only the angular mass and the
diagonal-block integral remain. -/
theorem realSchurMixedFlagCodedSource_gaussian_factor
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    (∫⁻ x in realSchurMixedFlagCodedSource s hs c hc R k code,
      ENNReal.ofReal (realSchurMixedJacobianWeight s 0 x *
        realMatrixGaussianWeight (RealSchurMixedCoord s) x.2.val)
        ∂realSchurMixedCoordinateVolume s) =
      (∫⁻ w in realSchurMixedFlagAnglePatch s hs c hc R k,
        ENNReal.ofReal |realSchurMixedAngularJacobian s w|) *
      ((∫⁻ d in realSchurMixedDiagonalCodeSource s code,
        ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian s d)) *
      ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
        Fintype.card (RealSchurMixedStrictUpperEntry s))) := by
  let F := fun w : RealSchurMixedOrbitIndex s → ℝ =>
    ENNReal.ofReal |realSchurMixedAngularJacobian s w|
  let G := fun d : RealSchurMixedDiagonalEntry s → ℝ =>
    ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian s d)
  let H := fun u : RealSchurMixedStrictUpperEntry s → ℝ =>
    ENNReal.ofReal (Real.exp (-(∑ p : RealSchurMixedStrictUpperEntry s, (u p)^2)/2))
  have hF : Measurable F :=
    (realSchurMixedAngularJacobian_continuous_of_shape s hs c hc).abs.measurable.ennreal_ofReal
  have hG : Measurable G :=
    (realSchurMixedDiagonalGaussianJacobian_continuous s).measurable.ennreal_ofReal
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hpoint (x : RealSchurMixedTangent s) :
      ENNReal.ofReal (realSchurMixedJacobianWeight s 0 x *
        realMatrixGaussianWeight (RealSchurMixedCoord s) x.2.val) =
      F (realSchurMixedTangentEntries s x).1 *
        (G (realSchurMixedTangentEntries s x).2.1 *
          H (realSchurMixedTangentEntries s x).2.2) := by
    let z := realSchurMixedUpperEntryEquiv s x.2
    have hx : realSchurMixedFiberPoint s x.1 z.1 z.2=x := by
      apply Prod.ext
      · rfl
      · exact (realSchurMixedUpperEntryEquiv s).symm_apply_apply x.2
    have hupper : realSchurMixedUpperEntryJoin s z.1 z.2=x.2.val :=
      congrArg (fun t : RealSchurMixedTangent s => t.2.val) hx
    have h := realSchurMixedFlagGaussian_fiber_factor s x.1 z.1 z.2
    rw [hx,hupper] at h
    rw [h, ENNReal.ofReal_mul (abs_nonneg _),
      ENNReal.ofReal_mul (realSchurMixedDiagonalGaussianJacobian_nonneg s z.1)]
    rfl
  simp_rw [hpoint]
  rw [realSchurMixedFlagCodedSource_lintegral_product s hs c hc R k code F G H hF hG hH]
  change _ = (∫⁻ w in realSchurMixedFlagAnglePatch s hs c hc R k, F w) *
    ((∫⁻ d in realSchurMixedDiagonalCodeSource s code, G d) * _)
  congr 2
  exact realSchurMixedStrictUpperGaussianLIntegral s

#print axioms realSchurMixedFlagCodedSource_gaussian_factor
end SpectralRadiusUpperTail
