import SpectralRadiusUpperTail.RealSchurMixedFlagAtlas
import SpectralRadiusUpperTail.RealSchurMixedRegularDisjointAtlas
import SpectralRadiusUpperTail.RealSchurMixedJacobianEverywhere
import Mathlib.Order.Disjointed

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- First-index patches are assigned to marker matrices, hence to
ordered orthogonal flags, rather than to sampled Schur matrices. -/
noncomputable def realSchurMixedFlagMarkerPatch
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ) :
    Set (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  disjointed (fun j =>
    (realSchurMixedMarkerRotatedChart s hs c hc (R j).val (R j).property).target) k

theorem measurableSet_realSchurMixedFlagMarkerPatch
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ) :
    MeasurableSet (realSchurMixedFlagMarkerPatch s hs c hc R k) :=
  MeasurableSet.disjointed
    (fun j => (realSchurMixedMarkerRotatedChart s hs c hc (R j).val (R j).property).open_target.measurableSet) k

theorem pairwise_realSchurMixedFlagMarkerPatch
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) :
    Pairwise (fun i j => Disjoint (realSchurMixedFlagMarkerPatch s hs c hc R i)
      (realSchurMixedFlagMarkerPatch s hs c hc R j)) :=
  disjoint_disjointed _

theorem exists_realSchurMixedFlagMarkerPatch
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s)
    (hcover : ∀ Q : RealSchurMixedOrthogonalFrame s, ∃ k,
      Q.val*realSchurMixedBlockScalar s c*Q.valᵀ ∈
        (realSchurMixedMarkerRotatedChart s hs c hc (R k).val (R k).property).target)
    (Q : RealSchurMixedOrthogonalFrame s) :
    ∃ k, Q.val*realSchurMixedBlockScalar s c*Q.valᵀ ∈
      realSchurMixedFlagMarkerPatch s hs c hc R k := by
  have hmem : Q.val*realSchurMixedBlockScalar s c*Q.valᵀ ∈
      ⋃ k, (realSchurMixedMarkerRotatedChart s hs c hc (R k).val (R k).property).target :=
    Set.mem_iUnion.mpr (hcover Q)
  rw [← iUnion_disjointed] at hmem
  exact Set.mem_iUnion.mp hmem

theorem realSchurMixedFlagMarker_continuous
    {m : ℕ} (s : Fin m → ℕ) (c : Fin m → ℝ) :
    Continuous (realSchurMixedFlagMarker s c) := by
  have h : Continuous (fun w : RealSchurMixedOrbitIndex s → ℝ =>
      realSchurMixedExpCoordinates s (realSchurMixedBlockScalar s c) (w,0)) :=
    (realSchurMixedExpCoordinates_contDiff s (realSchurMixedBlockScalar s c) 0).continuous.comp
      (continuous_id.prodMk continuous_const)
  apply h.congr
  intro w
  rw [realSchurMixedExpCoordinates_eq_conjugation]
  simp only [Submodule.coe_zero, add_zero]
  rfl

/-- The selected angle set is fixed independently of every actual
diagonal and strict-upper Schur entry. -/
noncomputable def realSchurMixedFlagAnglePatch
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ) :
    Set (RealSchurMixedOrbitIndex s → ℝ) :=
  realSchurMixedFlagDomain s hs c hc ∩
    (fun w => (R k).val*realSchurMixedFlagMarker s c w*(R k).valᵀ) ⁻¹'
      realSchurMixedFlagMarkerPatch s hs c hc R k

theorem measurableSet_realSchurMixedFlagAnglePatch
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ) :
    MeasurableSet (realSchurMixedFlagAnglePatch s hs c hc R k) := by
  have h : Continuous (fun w => (R k).val*realSchurMixedFlagMarker s c w*(R k).valᵀ) :=
    (continuous_const.mul (realSchurMixedFlagMarker_continuous s c)).mul continuous_const
  exact (realSchurMixedFlagDomain_open s hs c hc).measurableSet.inter
    ((measurableSet_realSchurMixedFlagMarkerPatch s hs c hc R k).preimage h.measurable)

#print axioms measurableSet_realSchurMixedFlagMarkerPatch
#print axioms pairwise_realSchurMixedFlagMarkerPatch
#print axioms exists_realSchurMixedFlagMarkerPatch
#print axioms realSchurMixedFlagMarker_continuous
#print axioms measurableSet_realSchurMixedFlagAnglePatch
end SpectralRadiusUpperTail
