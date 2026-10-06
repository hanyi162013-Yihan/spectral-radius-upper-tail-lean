import SpectralRadiusUpperTail.RealSchurMixedSpectralClassRepresentation
import SpectralRadiusUpperTail.RealSchurMixedIsospectralLocal
import SpectralRadiusUpperTail.RealSchurMixedSimpleRegular
import Mathlib.Topology.Connected.Clopen

namespace SpectralRadiusUpperTail
open Polynomial
open scoped Matrix Matrix.Norms.Operator Topology

/-- Along a continuous family with fixed simple characteristic
polynomial, existence of prescribed ordered Schur block polynomials is
both open and closed. Only block sizes one and two are used. -/
theorem isClopen_realSchurMixedSpectralClass_preimage
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2)
    (p : Fin m → ℝ[X]) {X : Type*} [TopologicalSpace X]
    (f : X → Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hf : Continuous f) (hsep : ∀ x, (f x).charpoly.Separable)
    (hpoly : ∀ x y, (f x).charpoly=(f y).charpoly) :
    IsClopen (f ⁻¹' realSchurMixedSpectralClass s p) := by
  have hspos : ∀ i, 0 < s i := by
    intro i
    rcases hs i with h | h <;> omega
  refine ⟨(isClosed_realSchurMixedSpectralClass s p).preimage hf,?_⟩
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨Q,T,hT,hdiag,hrep⟩ := (realSchurMixedSpectralClass_mem_iff s p (f x)).mp hx
  have hcp : (f x).charpoly=T.charpoly := by
    rw [hrep,realMatrixOrthogonalConjugation_charpoly _ _ _ Q.property]
  have hTs : T.charpoly.Separable := hcp ▸ hsep x
  have hreg := realSchurMixed_simpleSpectrum_orbit_det_ne_zero s hs T hT hTs
  obtain ⟨V,hVo,hV,hlocal⟩ :=
    realSchurMixed_isospectral_local_representation s hspos T hT hreg Q
  have hxV : x ∈ f ⁻¹' V := by
    change f x ∈ V
    rw [hrep]
    exact hV
  apply Filter.mem_of_superset ((hVo.preimage hf).mem_nhds hxV)
  intro y hy
  obtain ⟨P,U,hU,hUp,hUrep⟩ := hlocal (f y) hy ((hpoly y x).trans hcp)
  apply (realSchurMixedSpectralClass_mem_iff s p (f y)).mpr
  exact ⟨P,U,hU,fun a => (hUp a).trans (hdiag a),hUrep⟩

/-- On a connected isospectral family, a spectral class is represented
either everywhere or nowhere. -/
theorem realSchurMixedSpectralClass_connected_iff
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2)
    (p : Fin m → ℝ[X]) {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f : X → Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hf : Continuous f) (hsep : ∀ x, (f x).charpoly.Separable)
    (hpoly : ∀ x y, (f x).charpoly=(f y).charpoly) (x y : X) :
    f x ∈ realSchurMixedSpectralClass s p ↔ f y ∈ realSchurMixedSpectralClass s p := by
  have h := isClopen_realSchurMixedSpectralClass_preimage s hs p f hf hsep hpoly
  constructor
  · intro hx
    have hall := h.eq_univ ⟨x,hx⟩
    have hy : y ∈ f ⁻¹' realSchurMixedSpectralClass s p := by rw [hall]; trivial
    exact hy
  · intro hy
    have hall := h.eq_univ ⟨y,hy⟩
    have hx : x ∈ f ⁻¹' realSchurMixedSpectralClass s p := by rw [hall]; trivial
    exact hx

#print axioms isClopen_realSchurMixedSpectralClass_preimage
#print axioms realSchurMixedSpectralClass_connected_iff
end SpectralRadiusUpperTail
