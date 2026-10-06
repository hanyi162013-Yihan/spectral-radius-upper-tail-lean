import SpectralRadiusUpperTail.RealSchurMixedRegularGaussianIntegration
import SpectralRadiusUpperTail.RealSchurMixedRegularDisjointAtlas
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- A disjoint first-index target written in the fixed matrix-entry
coordinates used for the local Jacobian. -/
def realSchurMixedRegularEntryPatch
    {m : ℕ} {s : Fin m → ℕ}
    (c : ℕ → RealSchurMixedRegularFrame s) (k : ℕ) :
    Set (RealSchurMixedTangent s) :=
  realSchurMixedEntryEquiv s '' realSchurMixedRegularFirstPatch c k

theorem measurableSet_realSchurMixedRegularEntryPatch
    {m : ℕ} {s : Fin m → ℕ}
    (c : ℕ → RealSchurMixedRegularFrame s) (k : ℕ) :
    MeasurableSet (realSchurMixedRegularEntryPatch c k) := by
  have hEmb : MeasurableEmbedding (realSchurMixedEntryEquiv s) :=
    (realSchurMixedEntryEquiv s).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  exact hEmb.measurableSet_image'
    (measurableSet_realSchurMixedRegularFirstPatch c k)

theorem pairwise_realSchurMixedRegularEntryPatch
    {m : ℕ} {s : Fin m → ℕ}
    (c : ℕ → RealSchurMixedRegularFrame s) :
    Pairwise (fun i j => Disjoint
      (realSchurMixedRegularEntryPatch c i)
      (realSchurMixedRegularEntryPatch c j)) := by
  intro i j hij
  change Disjoint
    (realSchurMixedEntryEquiv s '' realSchurMixedRegularFirstPatch c i)
    (realSchurMixedEntryEquiv s '' realSchurMixedRegularFirstPatch c j)
  rw [Set.disjoint_image_iff (realSchurMixedEntryEquiv s).injective]
  exact pairwise_realSchurMixedRegularFirstPatch c hij

/-- The source of the first-index patch within its local inverse-function
chart. -/
def realSchurMixedRegularFirstSource
    {m : ℕ} {s : Fin m → ℕ}
    (c : ℕ → RealSchurMixedRegularFrame s) (k : ℕ) :
    Set (RealSchurMixedTangent s) :=
  (c k).chart.source ∩
    (realSchurMixedRotatedEntryCoordinates s (c k).T (c k).Q
      (c k).orthogonal) ⁻¹' realSchurMixedRegularEntryPatch c k

theorem measurableSet_realSchurMixedRegularFirstSource
    {m : ℕ} {s : Fin m → ℕ}
    (c : ℕ → RealSchurMixedRegularFrame s) (k : ℕ) :
    MeasurableSet (realSchurMixedRegularFirstSource c k) := by
  have hcont : Continuous
      (realSchurMixedRotatedEntryCoordinates s (c k).T (c k).Q
        (c k).orthogonal) :=
    (realSchurMixedOutputCoordinateEquiv s (c k).Q
      (c k).orthogonal).toContinuousLinearEquiv.continuous.comp
        (realSchurMixedEntryCoordinates_differentiable s (c k).T).continuous
  exact (c k).chart.open_source.measurableSet.inter
    ((measurableSet_realSchurMixedRegularEntryPatch c k).preimage hcont.measurable)

theorem realSchurMixedRegularFirstSource_subset_source
    {m : ℕ} {s : Fin m → ℕ}
    (c : ℕ → RealSchurMixedRegularFrame s) (k : ℕ) :
    realSchurMixedRegularFirstSource c k ⊆
      (realSchurMixedRegularChart s (c k).T (c k).regular).source := by
  intro x hx
  exact hx.1

/-- The selected source patch maps onto precisely its disjoint output
patch in fixed entry coordinates. -/
theorem realSchurMixedRegularFirstSource_image
    {m : ℕ} {s : Fin m → ℕ}
    (c : ℕ → RealSchurMixedRegularFrame s) (k : ℕ) :
    realSchurMixedRotatedEntryCoordinates s (c k).T (c k).Q
        (c k).orthogonal '' realSchurMixedRegularFirstSource c k =
      realSchurMixedRegularEntryPatch c k := by
  let f := realSchurMixedRotatedEntryCoordinates s (c k).T (c k).Q
    (c k).orthogonal
  have hf : f = (realSchurMixedEntryEquiv s) ∘ (c k).chart := by
    funext x
    exact realSchurMixedRotatedEntryCoordinates_eq s (c k).T (c k).Q
      (c k).orthogonal x |>.trans
        (congrArg (realSchurMixedEntryEquiv s)
          (realSchurMixedRegularRotatedChart_apply s (c k).T
            (c k).regular (c k).Q (c k).orthogonal x).symm)
  have hsource : f '' (c k).chart.source =
      realSchurMixedEntryEquiv s '' (c k).chart.target := by
    rw [hf, Set.image_comp, (c k).chart.image_source_eq_target]
  change f '' ((c k).chart.source ∩
    f ⁻¹' realSchurMixedRegularEntryPatch c k) = _
  rw [Set.image_inter_preimage, hsource]
  apply Set.inter_eq_right.mpr
  rintro y ⟨A,hA,rfl⟩
  exact ⟨A,hA.1,rfl⟩

/-- A first-index patch has the exact rotated real-Schur integral with
no overlap multiplicity. -/
theorem realSchurMixed_lintegral_first_patch
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : ℕ → RealSchurMixedRegularFrame s) (k : ℕ)
    (g : RealSchurMixedTangent s → ℝ≥0∞) :
    ∫⁻ y in realSchurMixedRegularEntryPatch c k,
        g y ∂realSchurMixedCoordinateVolume s =
      ∫⁻ x in realSchurMixedRegularFirstSource c k,
        ENNReal.ofReal (realSchurMixedJacobianWeight s (c k).T x) *
          g (realSchurMixedRotatedEntryCoordinates s (c k).T (c k).Q
            (c k).orthogonal x)
        ∂realSchurMixedCoordinateVolume s := by
  have h := realSchurMixed_lintegral_regular_rotated_chart s hs
    (c k).T (c k).Q (c k).upper (c k).regular (c k).orthogonal
    (realSchurMixedRegularFirstSource c k)
    (measurableSet_realSchurMixedRegularFirstSource c k)
    (realSchurMixedRegularFirstSource_subset_source c k) g
  rwa [realSchurMixedRegularFirstSource_image c k] at h

/-- Exact summation of local Jacobian integrals over the disjoint
regularly represented locus of one fixed block shape. -/
theorem realSchurMixed_lintegral_regular_patch_sum
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : ℕ → RealSchurMixedRegularFrame s)
    (g : RealSchurMixedTangent s → ℝ≥0∞) :
    ∫⁻ y in ⋃ k, realSchurMixedRegularEntryPatch c k,
        g y ∂realSchurMixedCoordinateVolume s =
      ∑' k, ∫⁻ x in realSchurMixedRegularFirstSource c k,
        ENNReal.ofReal (realSchurMixedJacobianWeight s (c k).T x) *
          g (realSchurMixedRotatedEntryCoordinates s (c k).T (c k).Q
            (c k).orthogonal x)
        ∂realSchurMixedCoordinateVolume s := by
  rw [lintegral_iUnion (measurableSet_realSchurMixedRegularEntryPatch c)
    (pairwise_realSchurMixedRegularEntryPatch c) g]
  congr 1
  funext k
  exact realSchurMixed_lintegral_first_patch s hs c k g

/-- Gaussian integration over the regular represented locus reduces to
a disjoint sum of explicit block-upper local integrals. -/
theorem realSchurMixed_gaussian_lintegral_regular_patch_sum
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : ℕ → RealSchurMixedRegularFrame s)
    (g : RealSchurMixedTangent s → ℝ≥0∞) :
    ∫⁻ y in ⋃ k, realSchurMixedRegularEntryPatch c k,
        ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y) * g y
        ∂realSchurMixedCoordinateVolume s =
      ∑' k, ∫⁻ x in realSchurMixedRegularFirstSource c k,
        ENNReal.ofReal (realSchurMixedJacobianWeight s (c k).T x) *
          (ENNReal.ofReal (realMatrixGaussianWeight
            (RealSchurMixedCoord s) ((c k).T+x.2.val)) *
            g (realSchurMixedRotatedEntryCoordinates s (c k).T (c k).Q
              (c k).orthogonal x))
        ∂realSchurMixedCoordinateVolume s := by
  have h := realSchurMixed_lintegral_regular_patch_sum s hs c
    (fun y => ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y) * g y)
  simpa only [realSchurMixedGaussianCoordinateWeight_rotated_chart,
    mul_assoc] using h

#print axioms realSchurMixed_lintegral_regular_patch_sum
#print axioms realSchurMixed_gaussian_lintegral_regular_patch_sum
end SpectralRadiusUpperTail
