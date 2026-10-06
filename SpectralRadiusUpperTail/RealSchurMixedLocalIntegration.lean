import SpectralRadiusUpperTail.RealSchurMixedJacobianEverywhere
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- Borel measurable structure on the finite-dimensional real-Schur
parameter space. -/
instance realSchurMixedTangentMeasurableSpace
    {m : ℕ} (s : Fin m → ℕ) :
    MeasurableSpace (RealSchurMixedTangent s) :=
  borel (RealSchurMixedTangent s)

instance realSchurMixedTangentBorelSpace
    {m : ℕ} (s : Fin m → ℕ) :
    BorelSpace (RealSchurMixedTangent s) := ⟨rfl⟩

instance realSchurMixedTangentNormBorelSpace
    {m : ℕ} (s : Fin m → ℕ) :
    @BorelSpace (RealSchurMixedTangent s)
      (inferInstance : NormedAddCommGroup (RealSchurMixedTangent s)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (realSchurMixedTangentMeasurableSpace s) := ⟨rfl⟩

/-- Fixed entry coordinates transport ordinary real matrix-entry
Lebesgue measure to the lower/upper parameter space. -/
noncomputable def realSchurMixedFlatEntryEquiv
    {m : ℕ} (s : Fin m → ℕ) :
    (RealSchurMixedCoord s × RealSchurMixedCoord s → ℝ) ≃ₗ[ℝ]
      RealSchurMixedTangent s :=
  (realMatrixEntryEquiv (RealSchurMixedCoord s)).symm.trans
    (realSchurMixedEntryEquiv s)

noncomputable def realSchurMixedCoordinateVolume
    {m : ℕ} (s : Fin m → ℕ) : Measure (RealSchurMixedTangent s) :=
  Measure.map (realSchurMixedFlatEntryEquiv s)
    (volume : Measure (RealSchurMixedCoord s × RealSchurMixedCoord s → ℝ))

theorem realSchurMixedCoordinateVolume_isAddHaarMeasure
    {m : ℕ} (s : Fin m → ℕ) :
    Measure.IsAddHaarMeasure (realSchurMixedCoordinateVolume s) := by
  change Measure.IsAddHaarMeasure (Measure.map (realSchurMixedFlatEntryEquiv s)
    (volume : Measure (RealSchurMixedCoord s × RealSchurMixedCoord s → ℝ)))
  exact Measure.MapLinearEquiv.isAddHaarMeasure
    (volume : Measure (RealSchurMixedCoord s × RealSchurMixedCoord s → ℝ))
    (realSchurMixedFlatEntryEquiv s)

instance realSchurMixedCoordinateVolume_normHaar
    {m : ℕ} (s : Fin m → ℕ) :
    @Measure.IsAddHaarMeasure (RealSchurMixedTangent s)
      (inferInstance : NormedAddCommGroup (RealSchurMixedTangent s)).toAddCommGroup.toAddGroup
      (inferInstance : NormedAddCommGroup (RealSchurMixedTangent s)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (realSchurMixedTangentMeasurableSpace s)
      (realSchurMixedCoordinateVolume s) := by
  convert! realSchurMixedCoordinateVolume_isAddHaarMeasure s

noncomputable def realSchurMixedJacobianWeight
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x : RealSchurMixedTangent s) : ℝ :=
  (∏ p : RealSchurLowerIndex m,
    |(realSchurMixedSylvester s (T+x.2.val) p).det|) *
      |realSchurMixedAngularJacobian s x.1|

theorem realSchurMixedJacobianWeight_eq_abs_det
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (x : RealSchurMixedTangent s) :
    realSchurMixedJacobianWeight s T x =
      |(fderiv ℝ (realSchurMixedEntryCoordinates s T) x).det| :=
  (realSchurMixedEntryCoordinates_fderiv_abs_det_everywhere s hs T hT x).symm

theorem realSchurMixedEntryCoordinates_injOn_source
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data) :
    Set.InjOn (realSchurMixedEntryCoordinates (fun i => (B i).size) T)
      (realSchurMixedLocalChart B T hT hdiag hsep).source := by
  intro x hx y hy he
  exact (realSchurMixedLocalChart B T hT hdiag hsep).injOn hx hy
    ((realSchurMixedEntryEquiv _).injective he)

theorem realSchurMixedEntryCoordinates_differentiable
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    Differentiable ℝ (realSchurMixedEntryCoordinates s T) := by
  intro x
  have hf := ((realSchurMixedExpCoordinates_contDiff s T 1).differentiable
    (by simp)) x
  convert! (realSchurMixedEntryEquiv s).toContinuousLinearEquiv.differentiableAt.comp
    x hf

/-- Local real-Schur change of variables on each measurable subset of
the constructed injective chart. -/
theorem realSchurMixed_lintegral_local_chart
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data)
    (U : Set (RealSchurMixedTangent (fun i => (B i).size)))
    (hU : MeasurableSet U)
    (hsub : U ⊆ (realSchurMixedLocalChart B T hT hdiag hsep).source)
    (g : RealSchurMixedTangent (fun i => (B i).size) → ℝ≥0∞) :
    ∫⁻ y in realSchurMixedEntryCoordinates (fun i => (B i).size) T '' U,
        g y ∂realSchurMixedCoordinateVolume (fun i => (B i).size) =
      ∫⁻ x in U,
        ENNReal.ofReal (realSchurMixedJacobianWeight
          (fun i => (B i).size) T x) *
          g (realSchurMixedEntryCoordinates (fun i => (B i).size) T x)
        ∂realSchurMixedCoordinateVolume (fun i => (B i).size) := by
  let s := fun i : Fin m => (B i).size
  let : Measure.IsAddHaarMeasure (realSchurMixedCoordinateVolume s) :=
    realSchurMixedCoordinateVolume_isAddHaarMeasure s
  have hupper : realSchurMixedLowerProjection s T = 0 := by
    apply (realSchurMixed_blockTriangular_iff_lower_zero s T).mp
    intro u v huv
    exact hT u.1 v.1 huv u.2 v.2
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (realSchurMixedCoordinateVolume s) hU
    (fun x _ => (realSchurMixedEntryCoordinates_differentiable s T x).hasFDerivAt.hasFDerivWithinAt)
    ((realSchurMixedEntryCoordinates_injOn_source B T hT hdiag hsep).mono hsub) g
  change (∫⁻ y in realSchurMixedEntryCoordinates s T '' U,
      g y ∂realSchurMixedCoordinateVolume s) =
    ∫⁻ x in U,
      ENNReal.ofReal (realSchurMixedJacobianWeight s T x) *
        g (realSchurMixedEntryCoordinates s T x)
      ∂realSchurMixedCoordinateVolume s
  simp only [realSchurMixedJacobianWeight_eq_abs_det s
    (fun i => (B i).size_pos) T hupper]
  exact h

/-- Local absolute-integrability equivalence; this prevents using a
formally defined but nonintegrable real integral as a density identity. -/
theorem realSchurMixed_integrableOn_local_chart_iff
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data)
    (U : Set (RealSchurMixedTangent (fun i => (B i).size)))
    (hU : MeasurableSet U)
    (hsub : U ⊆ (realSchurMixedLocalChart B T hT hdiag hsep).source)
    (g : RealSchurMixedTangent (fun i => (B i).size) → ℝ) :
    IntegrableOn g
      (realSchurMixedEntryCoordinates (fun i => (B i).size) T '' U)
      (realSchurMixedCoordinateVolume (fun i => (B i).size)) ↔
    IntegrableOn (fun x => realSchurMixedJacobianWeight
      (fun i => (B i).size) T x *
        g (realSchurMixedEntryCoordinates (fun i => (B i).size) T x)) U
      (realSchurMixedCoordinateVolume (fun i => (B i).size)) := by
  let s := fun i : Fin m => (B i).size
  let : Measure.IsAddHaarMeasure (realSchurMixedCoordinateVolume s) :=
    realSchurMixedCoordinateVolume_isAddHaarMeasure s
  have hupper : realSchurMixedLowerProjection s T = 0 := by
    apply (realSchurMixed_blockTriangular_iff_lower_zero s T).mp
    intro u v huv
    exact hT u.1 v.1 huv u.2 v.2
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (realSchurMixedCoordinateVolume s) hU
    (fun x _ => (realSchurMixedEntryCoordinates_differentiable s T x).hasFDerivAt.hasFDerivWithinAt)
    ((realSchurMixedEntryCoordinates_injOn_source B T hT hdiag hsep).mono hsub) g
  change IntegrableOn g (realSchurMixedEntryCoordinates s T '' U)
      (realSchurMixedCoordinateVolume s) ↔
    IntegrableOn (fun x => realSchurMixedJacobianWeight s T x *
      g (realSchurMixedEntryCoordinates s T x)) U
      (realSchurMixedCoordinateVolume s)
  simp only [realSchurMixedJacobianWeight_eq_abs_det s
    (fun i => (B i).size_pos) T hupper, smul_eq_mul]
  exact h

/-- Real integral change of variables on the actual local mixed Schur
chart, with its explicitly computed Jacobian. -/
theorem realSchurMixed_integral_local_chart
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data)
    (U : Set (RealSchurMixedTangent (fun i => (B i).size)))
    (hU : MeasurableSet U)
    (hsub : U ⊆ (realSchurMixedLocalChart B T hT hdiag hsep).source)
    (g : RealSchurMixedTangent (fun i => (B i).size) → ℝ) :
    ∫ y in realSchurMixedEntryCoordinates (fun i => (B i).size) T '' U,
        g y ∂realSchurMixedCoordinateVolume (fun i => (B i).size) =
      ∫ x in U,
        realSchurMixedJacobianWeight (fun i => (B i).size) T x *
          g (realSchurMixedEntryCoordinates (fun i => (B i).size) T x)
        ∂realSchurMixedCoordinateVolume (fun i => (B i).size) := by
  let s := fun i : Fin m => (B i).size
  let : Measure.IsAddHaarMeasure (realSchurMixedCoordinateVolume s) :=
    realSchurMixedCoordinateVolume_isAddHaarMeasure s
  have hupper : realSchurMixedLowerProjection s T = 0 := by
    apply (realSchurMixed_blockTriangular_iff_lower_zero s T).mp
    intro u v huv
    exact hT u.1 v.1 huv u.2 v.2
  have h := integral_image_eq_integral_abs_det_fderiv_smul
    (realSchurMixedCoordinateVolume s) hU
    (fun x _ => (realSchurMixedEntryCoordinates_differentiable s T x).hasFDerivAt.hasFDerivWithinAt)
    ((realSchurMixedEntryCoordinates_injOn_source B T hT hdiag hsep).mono hsub) g
  change (∫ y in realSchurMixedEntryCoordinates s T '' U,
      g y ∂realSchurMixedCoordinateVolume s) =
    ∫ x in U,
      realSchurMixedJacobianWeight s T x *
        g (realSchurMixedEntryCoordinates s T x)
      ∂realSchurMixedCoordinateVolume s
  simp only [realSchurMixedJacobianWeight_eq_abs_det s
    (fun i => (B i).size_pos) T hupper, smul_eq_mul]
  exact h

#print axioms realSchurMixed_lintegral_local_chart
#print axioms realSchurMixed_integrableOn_local_chart_iff
#print axioms realSchurMixed_integral_local_chart
end SpectralRadiusUpperTail
