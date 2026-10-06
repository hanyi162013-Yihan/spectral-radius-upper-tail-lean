import SpectralRadiusUpperTail.RealSchurMixedMarkerChart
import SpectralRadiusUpperTail.RealSchurBlockMarker

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

noncomputable def realSchurMixedFlagMarker
    {m : ℕ} (s : Fin m → ℕ) (c : Fin m → ℝ)
    (w : RealSchurMixedOrbitIndex s → ℝ) :
    Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
  realSchurBlockMarker (fun i : RealSchurMixedCoord s => i.1) c
    (realSchurMixedAngularFrame s w)

/-- The angle domain is a slice of a fixed marker chart. It contains no
random diagonal-block or strict-upper entries. -/
noncomputable def realSchurMixedFlagDomain
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c) :
    Set (RealSchurMixedOrbitIndex s → ℝ) :=
  (fun w => (w,(0 : realSchurMixedUpperSubmodule s))) ⁻¹'
    (realSchurMixedMarkerChart s hs c hc).source

theorem realSchurMixedFlagDomain_open
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c) :
    IsOpen (realSchurMixedFlagDomain s hs c hc) :=
  (realSchurMixedMarkerChart s hs c hc).open_source.preimage
    (continuous_id.prodMk continuous_const)

theorem realSchurMixedFlagDomain_zero
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c) :
    0 ∈ realSchurMixedFlagDomain s hs c hc :=
  realSchurMixedMarkerChart_zero_mem_source s hs c hc

theorem realSchurMixedFlagMarker_eq_chart
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (w : RealSchurMixedOrbitIndex s → ℝ) :
    realSchurMixedFlagMarker s c w = realSchurMixedMarkerChart s hs c hc (w,0) := by
  rw [realSchurMixedMarkerChart_apply, realSchurMixedExpCoordinates_eq_conjugation]
  simp only [Submodule.coe_zero, add_zero]
  rfl

theorem realSchurMixedFlagMarker_injOn
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c) :
    Set.InjOn (realSchurMixedFlagMarker s c) (realSchurMixedFlagDomain s hs c hc) := by
  intro u hu v hv heq
  rw [realSchurMixedFlagMarker_eq_chart s hs c hc,
    realSchurMixedFlagMarker_eq_chart s hs c hc] at heq
  exact congrArg Prod.fst ((realSchurMixedMarkerChart s hs c hc).injOn hu hv heq)

/-- Every symmetric matrix with the marker characteristic polynomial
in the local target has a purely angular preimage. -/
theorem realSchurMixedFlagMarker_local_coverage
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hA : A ∈ (realSchurMixedMarkerChart s hs c hc).target)
    (hHerm : A.IsHermitian)
    (hpoly : A.charpoly = (realSchurMixedBlockScalar s c).charpoly) :
    ∃ w ∈ realSchurMixedFlagDomain s hs c hc,
      realSchurMixedFlagMarker s c w = A := by
  let C := realSchurMixedMarkerChart s hs c hc
  let x := C.symm A
  have hx : x ∈ C.source := C.map_target hA
  have hmap : C x = A := C.right_inv hA
  have hz : x.2 = 0 := realSchurMixedMarkerChart_upper_zero s hs c hc x hx
    (hmap.symm ▸ hHerm) (hmap.symm ▸ hpoly)
  have hpair : (x.1,(0 : realSchurMixedUpperSubmodule s)) = x := by
    exact Prod.ext rfl hz.symm
  refine ⟨x.1,?_,?_⟩
  · change (x.1,(0 : realSchurMixedUpperSubmodule s)) ∈ C.source
    rwa [hpair]
  · rw [realSchurMixedFlagMarker_eq_chart s hs c hc, hpair]
    exact hmap

/-- On a local angle domain, the full Schur representation is injective
when the ordered diagonal-block spectra are fixed. The upper matrix
entries remain unrestricted. -/
theorem realSchurMixedFlag_full_injective_ordered
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (u v : RealSchurMixedOrbitIndex s → ℝ)
    (hu : u ∈ realSchurMixedFlagDomain s hs c hc)
    (hv : v ∈ realSchurMixedFlagDomain s hs c hc)
    (T U : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : T.BlockTriangular (fun i : RealSchurMixedCoord s => i.1))
    (hU : U.BlockTriangular (fun i : RealSchurMixedCoord s => i.1))
    (hsep : T.charpoly.Separable)
    (hdiag : ∀ a : Fin m,
      (U.toSquareBlock (fun i : RealSchurMixedCoord s => i.1) a).charpoly =
        (T.toSquareBlock (fun i : RealSchurMixedCoord s => i.1) a).charpoly)
    (heq : realSchurMixedAngularFrame s u*T*(realSchurMixedAngularFrame s u)ᵀ =
      realSchurMixedAngularFrame s v*U*(realSchurMixedAngularFrame s v)ᵀ) :
    u=v ∧ T=U := by
  have hmarker := realSchurBlockMarker_eq_of_ordered_spectra
    (fun i : RealSchurMixedCoord s => i.1) c _
    (realSchurMixedAngularFrame s u) (realSchurMixedAngularFrame s v) T U
    (realSchurMixedAngularFrame_orthogonal s u)
    (realSchurMixedAngularFrame_orthogonal s v) hT hU rfl heq hsep hdiag
  have huv : u=v := realSchurMixedFlagMarker_injOn s hs c hc hu hv hmarker
  refine ⟨huv,?_⟩
  rw [← huv] at heq
  exact (realMatrixOrthogonalConjugationEquiv _ (realSchurMixedAngularFrame s u)
    (realSchurMixedAngularFrame_orthogonal s u)).injective heq

#print axioms realSchurMixedFlagDomain_open
#print axioms realSchurMixedFlagDomain_zero
#print axioms realSchurMixedFlagMarker_eq_chart
#print axioms realSchurMixedFlagMarker_injOn
#print axioms realSchurMixedFlagMarker_local_coverage
#print axioms realSchurMixedFlag_full_injective_ordered
end SpectralRadiusUpperTail
