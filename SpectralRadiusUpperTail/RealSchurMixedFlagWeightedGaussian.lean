import SpectralRadiusUpperTail.RealSchurMixedFlagEntryFubini
import SpectralRadiusUpperTail.RealSchurMixedFlagGaussianFactors
import SpectralRadiusUpperTail.RealSchurMixedCodeClassFiber

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator BigOperators

theorem realSchurMixedFlagGaussian_entry_factor
    {m : ℕ} (s : Fin m → ℕ) (x : RealSchurMixedTangent s) :
    ENNReal.ofReal (realSchurMixedJacobianWeight s 0 x) *
      ENNReal.ofReal (realMatrixGaussianWeight (RealSchurMixedCoord s) x.2.val) =
      ENNReal.ofReal |realSchurMixedAngularJacobian s (realSchurMixedTangentEntries s x).1| *
        (ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian s (realSchurMixedTangentEntries s x).2.1) *
          ENNReal.ofReal (Real.exp (-(∑ p : RealSchurMixedStrictUpperEntry s,
            ((realSchurMixedTangentEntries s x).2.2 p)^2)/2))) := by
  let z := realSchurMixedUpperEntryEquiv s x.2
  have hx : realSchurMixedFiberPoint s x.1 z.1 z.2=x := by
    apply Prod.ext
    · rfl
    · exact (realSchurMixedUpperEntryEquiv s).symm_apply_apply x.2
  have hupper : realSchurMixedUpperEntryJoin s z.1 z.2=x.2.val :=
    congrArg (fun t : RealSchurMixedTangent s => t.2.val) hx
  have hJ : 0 ≤ realSchurMixedJacobianWeight s 0 x :=
    mul_nonneg (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) (abs_nonneg _)
  have h := realSchurMixedFlagGaussian_fiber_factor s x.1 z.1 z.2
  rw [hx,hupper] at h
  rw [← ENNReal.ofReal_mul hJ,h,ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.ofReal_mul (realSchurMixedDiagonalGaussianJacobian_nonneg s z.1)]
  rfl

/-- A measurable diagonal weight remains outside the full strict-upper
Gaussian integral, even for a general nonnegative matrix observable. -/
theorem realSchurMixedFlagCodedSource_weighted_gaussian
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (W : (RealSchurMixedDiagonalEntry s → ℝ) → ℝ≥0∞)
    (H : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ → ℝ≥0∞)
    (hW : Measurable W) (hH : Measurable H) :
    (∫⁻ x in realSchurMixedFlagCodedSource s hs c hc R k code,
      ENNReal.ofReal (realSchurMixedJacobianWeight s 0 x) *
        (ENNReal.ofReal (realMatrixGaussianWeight (RealSchurMixedCoord s) x.2.val) *
          (W (realSchurMixedTangentEntries s x).2.1 * H x.2.val))
        ∂realSchurMixedCoordinateVolume s) =
      (∫⁻ w in realSchurMixedFlagAnglePatch s hs c hc R k,
        ENNReal.ofReal |realSchurMixedAngularJacobian s w|) *
      (∫⁻ d in realSchurMixedDiagonalCodeSource s code,
        (ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian s d)*W d) *
          (∫⁻ u : RealSchurMixedStrictUpperEntry s → ℝ,
            ENNReal.ofReal (Real.exp (-(∑ p, (u p)^2)/2)) *
              H (realSchurMixedUpperEntryJoin s d u))) := by
  let F := fun w => ENNReal.ofReal |realSchurMixedAngularJacobian s w|
  let K := fun z : (RealSchurMixedDiagonalEntry s → ℝ) ×
      (RealSchurMixedStrictUpperEntry s → ℝ) =>
    (ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian s z.1)*W z.1) *
      (ENNReal.ofReal (Real.exp (-(∑ p, (z.2 p)^2)/2))*H (realSchurMixedUpperEntryJoin s z.1 z.2))
  have hF : Measurable F :=
    (realSchurMixedAngularJacobian_continuous_of_shape s hs c hc).abs.measurable.ennreal_ofReal
  have hDiag := (realSchurMixedDiagonalGaussianJacobian_continuous s).measurable.ennreal_ofReal
  have hJoin := (realSchurMixedUpperEntryJoin_continuous s).measurable
  have hGauss : Measurable (fun u : RealSchurMixedStrictUpperEntry s → ℝ =>
      ENNReal.ofReal (Real.exp (-(∑ p, (u p)^2)/2))) := by fun_prop
  have hK : Measurable K := by
    dsimp [K]
    exact ((hDiag.comp measurable_fst).mul (hW.comp measurable_fst)).mul
      ((hGauss.comp measurable_snd).mul (hH.comp hJoin))
  have hpoint (x : RealSchurMixedTangent s) :
      ENNReal.ofReal (realSchurMixedJacobianWeight s 0 x) *
        (ENNReal.ofReal (realMatrixGaussianWeight (RealSchurMixedCoord s) x.2.val) *
          (W (realSchurMixedTangentEntries s x).2.1*H x.2.val)) =
      F (realSchurMixedTangentEntries s x).1*K (realSchurMixedTangentEntries s x).2 := by
    have hupper : realSchurMixedUpperEntryJoin s (realSchurMixedTangentEntries s x).2.1
        (realSchurMixedTangentEntries s x).2.2=x.2.val :=
      congrArg Subtype.val ((realSchurMixedUpperEntryEquiv s).symm_apply_apply x.2)
    rw [← mul_assoc,realSchurMixedFlagGaussian_entry_factor]
    dsimp only [F,K]
    rw [hupper]
    ac_rfl
  simp_rw [hpoint]
  rw [realSchurMixedFlagCodedSource_lintegral_entry_fubini s hs c hc R k code F K hF hK]
  congr 1
  apply lintegral_congr
  intro d
  have hd : Continuous (fun u : RealSchurMixedStrictUpperEntry s → ℝ =>
      realSchurMixedUpperEntryJoin s d u) :=
    (realSchurMixedUpperEntryJoin_continuous s).comp (continuous_const.prodMk continuous_id)
  dsimp only [K]
  exact lintegral_const_mul _ (hGauss.mul (hH.comp hd.measurable))

#print axioms realSchurMixedFlagGaussian_entry_factor
#print axioms realSchurMixedFlagCodedSource_weighted_gaussian
end SpectralRadiusUpperTail
