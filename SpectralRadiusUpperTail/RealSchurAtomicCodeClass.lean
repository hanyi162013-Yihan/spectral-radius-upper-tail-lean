import SpectralRadiusUpperTail.RealSchurAtomicCodeTest
import SpectralRadiusUpperTail.RealSchurMixedCodeClassImage

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- An intrinsic code class restricted to scalar and nonreal-pair blocks. -/
def realSchurAtomicCodeClass {m : ℕ} (s : Fin m → ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    Set (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  realSchurMixedCodeClass s code ∩ {A | realSchurAtomicCodeTest s code A}

theorem measurableSet_realSchurAtomicCodeClass
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    MeasurableSet (realSchurAtomicCodeClass s code) :=
  (measurableSet_realSchurMixedCodeClass s hs code).inter (measurableSet_realSchurAtomicCodeTest s code)

theorem realSchurAtomicCodeClass_mem_iff
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    A ∈ realSchurAtomicCodeClass s code ↔
      ∃ Q : RealSchurMixedOrthogonalFrame s,
        ∃ T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ,
          realSchurMixedLowerProjection s T=0 ∧ T.charpoly.Separable ∧
          realSchurMixedSpectralCode s T=code ∧ realSchurMixedAtomicBlocks s T ∧ A=Q.val*T*Q.valᵀ := by
  constructor
  · rintro ⟨⟨Q,T,hT,hsep,hcode,hrep⟩,htest⟩
    have hcp : A.charpoly=T.charpoly := by
      rw [hrep,realMatrixOrthogonalConjugation_charpoly _ _ _ Q.property]
    have hAs : A.charpoly.Separable := hcp.symm ▸ hsep
    have htestT := (realSchurAtomicCodeTest_iff_of_charpoly s code A T hAs hsep hcp).mp htest
    rw [← hcode] at htestT
    exact ⟨Q,T,hT,hsep,hcode,(realSchurMixedAtomicBlocks_iff_codeTest s hs T hT hsep).mpr htestT,hrep⟩
  · rintro ⟨Q,T,hT,hsep,hcode,hatomic,hrep⟩
    refine ⟨⟨Q,T,hT,hsep,hcode,hrep⟩,?_⟩
    have hcp : A.charpoly=T.charpoly := by
      rw [hrep,realMatrixOrthogonalConjugation_charpoly _ _ _ Q.property]
    have hAs : A.charpoly.Separable := hcp.symm ▸ hsep
    have htest := (realSchurMixedAtomicBlocks_iff_codeTest s hs T hT hsep).mp hatomic
    rw [hcode] at htest
    exact (realSchurAtomicCodeTest_iff_of_charpoly s code A T hAs hsep hcp).mpr htest

theorem realSchurAtomicCodeClass_connected_iff
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f : X → Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hf : Continuous f) (hsep : ∀ x, (f x).charpoly.Separable)
    (hpoly : ∀ x y, (f x).charpoly=(f y).charpoly) (x y : X) :
    f x ∈ realSchurAtomicCodeClass s code ↔ f y ∈ realSchurAtomicCodeClass s code :=
  and_congr (realSchurMixedCodeClass_connected_iff s hs code f hf hsep hpoly x y)
    (realSchurAtomicCodeTest_iff_of_charpoly s code (f x) (f y) (hsep x) (hsep y) (hpoly x y))

#print axioms measurableSet_realSchurAtomicCodeClass
#print axioms realSchurAtomicCodeClass_mem_iff
#print axioms realSchurAtomicCodeClass_connected_iff
end SpectralRadiusUpperTail
