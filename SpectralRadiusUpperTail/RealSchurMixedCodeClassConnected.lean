import SpectralRadiusUpperTail.RealSchurMixedSpectralClassConnected
import SpectralRadiusUpperTail.RealSchurMixedSpectralFiber

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- A simple matrix belongs to a code class when that ordered spectral
assignment is realized by some orthogonal block-upper representation. -/
def realSchurMixedCodeClass
    {m : ℕ} (s : Fin m → ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    Set (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  {A | ∃ Q : RealSchurMixedOrthogonalFrame s,
    ∃ T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ,
      realSchurMixedLowerProjection s T=0 ∧ T.charpoly.Separable ∧
      realSchurMixedSpectralCode s T=code ∧ A=Q.val*T*Q.valᵀ}

/-- Realized finite spectral codes are constant on connected families
of matrices with fixed simple characteristic polynomial. -/
theorem realSchurMixedCodeClass_connected_iff
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f : X → Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hf : Continuous f) (hsep : ∀ x, (f x).charpoly.Separable)
    (hpoly : ∀ x y, (f x).charpoly=(f y).charpoly) (x y : X) :
    f x ∈ realSchurMixedCodeClass s code ↔ f y ∈ realSchurMixedCodeClass s code := by
  have hspos : ∀ i, 0 < s i := by
    intro i
    rcases hs i with h | h <;> omega
  have hforward (x y : X) (hx : f x ∈ realSchurMixedCodeClass s code) :
      f y ∈ realSchurMixedCodeClass s code := by
    obtain ⟨Q,T,hT,hTs,hcode,hrep⟩ := hx
    let p := fun a => (realSchurMixedDiagonalMatrix s T a).charpoly
    have hxclass : f x ∈ realSchurMixedSpectralClass s p :=
      (realSchurMixedSpectralClass_mem_iff s p (f x)).mpr ⟨Q,T,hT,fun _ => rfl,hrep⟩
    have hyclass := (realSchurMixedSpectralClass_connected_iff
      s hs p f hf hsep hpoly x y).mp hxclass
    obtain ⟨P,U,hU,hUp,hUrep⟩ := (realSchurMixedSpectralClass_mem_iff s p (f y)).mp hyclass
    have hcp : (f y).charpoly=U.charpoly := by
      rw [hUrep,realMatrixOrthogonalConjugation_charpoly _ _ _ P.property]
    have hUs : U.charpoly.Separable := hcp ▸ hsep y
    have hcodeU := realSchurMixedSpectralCode_eq_of_diagonal_polynomials
      s hspos U T hU hT hUs hUp
    exact ⟨P,U,hU,hUs,hcodeU.trans hcode,hUrep⟩
  exact ⟨hforward x y,hforward y x⟩

#print axioms realSchurMixedCodeClass_connected_iff
end SpectralRadiusUpperTail
