import SpectralRadiusUpperTail.RealSchurAtomicFlagSource
import SpectralRadiusUpperTail.RealSchurMixedFlagWeightedGaussian

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

theorem realSchurAtomicFlagSource_mem_iff_entries
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (x : RealSchurMixedTangent s) :
    x ∈ realSchurAtomicFlagSource s hs c hc R k code ↔
      (realSchurMixedTangentEntries s x).1 ∈ realSchurMixedFlagAnglePatch s hs c hc R k ∧
        (realSchurMixedTangentEntries s x).2.1 ∈ realSchurAtomicDiagonalSource s code := by
  have hx : realSchurMixedFiberPoint s x.1
      (realSchurMixedUpperEntryEquiv s x.2).1
      (realSchurMixedUpperEntryEquiv s x.2).2 = x := by
    apply Prod.ext
    · rfl
    · exact (realSchurMixedUpperEntryEquiv s).symm_apply_apply x.2
  have h := realSchurAtomicFlagSource_full_fiber s hs c hc R k code x.1
    (realSchurMixedUpperEntryEquiv s x.2).1 (realSchurMixedUpperEntryEquiv s x.2).2
  simpa only [hx, realSchurMixedTangentEntries] using h

/-- Tonelli on a selected coded source, for a general observable of
the diagonal and strict-upper entries. The inner integral ranges over
the entire strict-upper array. -/
theorem realSchurAtomicFlagSource_lintegral_entry_fubini
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (F : (RealSchurMixedOrbitIndex s → ℝ) → ℝ≥0∞)
    (K : ((RealSchurMixedDiagonalEntry s → ℝ) ×
      (RealSchurMixedStrictUpperEntry s → ℝ)) → ℝ≥0∞)
    (hF : Measurable F) (hK : Measurable K) :
    (∫⁻ x in realSchurAtomicFlagSource s hs c hc R k code,
      F (realSchurMixedTangentEntries s x).1*K (realSchurMixedTangentEntries s x).2
        ∂realSchurMixedCoordinateVolume s) =
      (∫⁻ w in realSchurMixedFlagAnglePatch s hs c hc R k, F w) *
        (∫⁻ d in realSchurAtomicDiagonalSource s code, ∫⁻ u, K (d,u)) := by
  classical
  let A := realSchurMixedFlagAnglePatch s hs c hc R k
  let D := realSchurAtomicDiagonalSource s code
  let S := realSchurAtomicFlagSource s hs c hc R k code
  have hA : MeasurableSet A := measurableSet_realSchurMixedFlagAnglePatch s hs c hc R k
  have hD : MeasurableSet D := measurableSet_realSchurAtomicDiagonalSource s code
  have hS : MeasurableSet S := measurableSet_realSchurAtomicFlagSource s hs c hc R k code
  let K' := (Prod.fst ⁻¹' D).indicator K
  have hK' : Measurable K' := hK.indicator (hD.preimage measurable_fst)
  have hpoint (x : RealSchurMixedTangent s) :
      S.indicator (fun x => F (realSchurMixedTangentEntries s x).1 *
        K (realSchurMixedTangentEntries s x).2) x =
      A.indicator F (realSchurMixedTangentEntries s x).1 *
        K' (realSchurMixedTangentEntries s x).2 := by
    have hm : x ∈ S ↔ (realSchurMixedTangentEntries s x).1 ∈ A ∧
        (realSchurMixedTangentEntries s x).2.1 ∈ D :=
      realSchurAtomicFlagSource_mem_iff_entries s hs c hc R k code x
    by_cases ha : (realSchurMixedTangentEntries s x).1 ∈ A <;>
      by_cases hd : (realSchurMixedTangentEntries s x).2.1 ∈ D <;>
        simp [K',Set.mem_preimage,hm,ha,hd]
  change (∫⁻ x in S, F (realSchurMixedTangentEntries s x).1 *
    K (realSchurMixedTangentEntries s x).2 ∂realSchurMixedCoordinateVolume s)=_
  rw [← lintegral_indicator hS]
  simp_rw [hpoint]
  rw [realSchurMixed_lintegral_angle_entryProduct s (A.indicator F) K' (hF.indicator hA) hK',
    lintegral_indicator hA]
  congr 1
  have hinner (d : RealSchurMixedDiagonalEntry s → ℝ) :
      (∫⁻ u, K' (d,u))=D.indicator (fun d => ∫⁻ u, K (d,u)) d := by
    by_cases hd : d ∈ D <;> simp [K',Set.mem_preimage,hd]
  simp_rw [hinner]
  exact lintegral_indicator hD _

/-- A measurable diagonal weight remains outside the full strict-upper
Gaussian integral, even for a general nonnegative matrix observable. -/
theorem realSchurAtomicFlagSource_weighted_gaussian
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (W : (RealSchurMixedDiagonalEntry s → ℝ) → ℝ≥0∞)
    (H : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ → ℝ≥0∞)
    (hW : Measurable W) (hH : Measurable H) :
    (∫⁻ x in realSchurAtomicFlagSource s hs c hc R k code,
      ENNReal.ofReal (realSchurMixedJacobianWeight s 0 x) *
        (ENNReal.ofReal (realMatrixGaussianWeight (RealSchurMixedCoord s) x.2.val) *
          (W (realSchurMixedTangentEntries s x).2.1 * H x.2.val))
        ∂realSchurMixedCoordinateVolume s) =
      (∫⁻ w in realSchurMixedFlagAnglePatch s hs c hc R k,
        ENNReal.ofReal |realSchurMixedAngularJacobian s w|) *
      (∫⁻ d in realSchurAtomicDiagonalSource s code,
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
  rw [realSchurAtomicFlagSource_lintegral_entry_fubini s hs c hc R k code F K hF hK]
  congr 1
  apply lintegral_congr
  intro d
  have hd : Continuous (fun u : RealSchurMixedStrictUpperEntry s → ℝ =>
      realSchurMixedUpperEntryJoin s d u) :=
    (realSchurMixedUpperEntryJoin_continuous s).comp (continuous_const.prodMk continuous_id)
  dsimp only [K]
  exact lintegral_const_mul _ (hGauss.mul (hH.comp hd.measurable))

#print axioms realSchurAtomicFlagSource_mem_iff_entries
#print axioms realSchurAtomicFlagSource_lintegral_entry_fubini
#print axioms realSchurAtomicFlagSource_weighted_gaussian
end SpectralRadiusUpperTail
