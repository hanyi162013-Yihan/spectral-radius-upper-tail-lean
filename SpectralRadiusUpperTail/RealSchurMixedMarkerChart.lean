import SpectralRadiusUpperTail.RealSchurMixedMarkerIsolation
import SpectralRadiusUpperTail.RealSchurMixedRegularChart
import SpectralRadiusUpperTail.RealSchurMixedChartSpectrum

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

noncomputable def realSchurMixedMarkerNeighborhood
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i) (c : Fin m → ℝ) :
    Set (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  (exists_open_realSchurMixed_marker_isolation s hs c).choose

theorem realSchurMixedMarkerNeighborhood_open
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i) (c : Fin m → ℝ) :
    IsOpen (realSchurMixedMarkerNeighborhood s hs c) :=
  (exists_open_realSchurMixed_marker_isolation s hs c).choose_spec.1

theorem realSchurMixedMarkerNeighborhood_mem
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i) (c : Fin m → ℝ) :
    realSchurMixedBlockScalar s c ∈ realSchurMixedMarkerNeighborhood s hs c :=
  (exists_open_realSchurMixed_marker_isolation s hs c).choose_spec.2.1

theorem realSchurMixedMarkerNeighborhood_eq
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i) (c : Fin m → ℝ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : T ∈ realSchurMixedMarkerNeighborhood s hs c)
    (hHerm : T.IsHermitian) (hLower : realSchurMixedLowerProjection s T = 0)
    (hpoly : T.charpoly = (realSchurMixedBlockScalar s c).charpoly) :
    T = realSchurMixedBlockScalar s c :=
  (exists_open_realSchurMixed_marker_isolation s hs c).choose_spec.2.2
    T hT hHerm hLower hpoly

/-- A full inverse-function chart, restricted by a fixed marker slice.
The restriction will force the upper variation to vanish on the marker
orbit, yielding a genuine local chart for the ordered orthogonal flag. -/
noncomputable def realSchurMixedMarkerChart
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c) :
    OpenPartialHomeomorph (RealSchurMixedTangent s)
      (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  (realSchurMixedRegularChart s (realSchurMixedBlockScalar s c)
    (realSchurMixedBlockScalar_orbit_det_ne_zero s hs c hc)).restrOpen
      ((fun x : RealSchurMixedTangent s => realSchurMixedBlockScalar s c + x.2.val) ⁻¹'
        realSchurMixedMarkerNeighborhood s hs c)
      ((realSchurMixedMarkerNeighborhood_open s hs c).preimage
        (continuous_const.add (realSchurMixedUpperTangentCLM s).continuous))

theorem realSchurMixedMarkerChart_apply
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c) (x : RealSchurMixedTangent s) :
    realSchurMixedMarkerChart s hs c hc x =
      realSchurMixedExpCoordinates s (realSchurMixedBlockScalar s c) x := rfl

theorem realSchurMixedMarkerChart_zero_mem_source
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c) :
    0 ∈ (realSchurMixedMarkerChart s hs c hc).source := by
  constructor
  · exact realSchurMixedRegularChart_zero_mem_source s _ _
  · change realSchurMixedBlockScalar s c + 0 ∈ realSchurMixedMarkerNeighborhood s hs c
    simpa only [add_zero] using
      realSchurMixedMarkerNeighborhood_mem s hs c

/-- On the marker orbit, the full chart inverse has no upper variation.
Thus its only effective parameter is the orthogonal block flag. -/
theorem realSchurMixedMarkerChart_upper_zero
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (x : RealSchurMixedTangent s)
    (hx : x ∈ (realSchurMixedMarkerChart s hs c hc).source)
    (hHerm : (realSchurMixedMarkerChart s hs c hc x).IsHermitian)
    (hpoly : (realSchurMixedMarkerChart s hs c hc x).charpoly =
      (realSchurMixedBlockScalar s c).charpoly) : x.2 = 0 := by
  let D := realSchurMixedBlockScalar s c
  let Q := realSchurMixedAngularFrame s x.1
  have hQ : Qᵀ*Q=1 := realSchurMixedAngularFrame_orthogonal s x.1
  have hrecover : D+x.2.val = Qᵀ*(realSchurMixedMarkerChart s hs c hc x)*Q := by
    rw [realSchurMixedMarkerChart_apply, realSchurMixedExpCoordinates_eq_conjugation]
    change D+x.2.val = Qᵀ*(Q*(D+x.2.val)*Qᵀ)*Q
    simp only [Matrix.mul_assoc, hQ, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have hHermT : (D+x.2.val).IsHermitian := by
    rw [hrecover]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul Q hHerm
  have hLower : realSchurMixedLowerProjection s (D+x.2.val) = 0 := by
    rw [map_add, realSchurMixedBlockScalar_lower_zero, zero_add]
    exact x.2.property
  have hpolyT : (D+x.2.val).charpoly = D.charpoly := by
    rw [realSchurMixedMarkerChart_apply, realSchurMixedExpCoordinates_eq_conjugation,
      realMatrixOrthogonalConjugation_charpoly _ _ _
        (realSchurMixedAngularFrame_orthogonal s x.1)] at hpoly
    exact hpoly
  have heq := realSchurMixedMarkerNeighborhood_eq s hs c (D+x.2.val)
    hx.2 hHermT hLower hpolyT
  apply Subtype.ext
  exact add_left_cancel (heq.trans (add_zero D).symm)

#print axioms realSchurMixedMarkerNeighborhood_open
#print axioms realSchurMixedMarkerNeighborhood_mem
#print axioms realSchurMixedMarkerNeighborhood_eq
#print axioms realSchurMixedMarkerChart_apply
#print axioms realSchurMixedMarkerChart_zero_mem_source
#print axioms realSchurMixedMarkerChart_upper_zero
end SpectralRadiusUpperTail
