import SpectralRadiusUpperTail.RealSchurAtomicCodeClass
import SpectralRadiusUpperTail.RealSchurFixedAtomicBlocks
import SpectralRadiusUpperTail.RealSchurFiniteCodeCoverage

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator BigOperators

def realSchurFiniteAtomicClass {n : ℕ} (I : RealSchurFiniteCode n) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.reindex I.2.1 I.2.1) ⁻¹' realSchurAtomicCodeClass I.1.sizes I.2.2

theorem measurableSet_realSchurFiniteAtomicClass
    {n : ℕ} (I : RealSchurFiniteCode n) : MeasurableSet (realSchurFiniteAtomicClass I) :=
  (measurableSet_realSchurAtomicCodeClass I.1.sizes I.1.sizes_pos I.2.2).preimage
    (realSchur_reindex_continuous I.2.1).measurable

theorem realSchurFiniteAtomicClass_connected_iff
    {n : ℕ} (I : RealSchurFiniteCode n)
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f : X → Matrix (Fin n) (Fin n) ℝ) (hf : Continuous f)
    (hsep : ∀ x, (f x).charpoly.Separable)
    (hpoly : ∀ x y, (f x).charpoly=(f y).charpoly) (x y : X) :
    f x ∈ realSchurFiniteAtomicClass I ↔ f y ∈ realSchurFiniteAtomicClass I := by
  apply realSchurAtomicCodeClass_connected_iff I.1.sizes I.1.sizes_small I.2.2
    (fun z => Matrix.reindex I.2.1 I.2.1 (f z))
  · exact (realSchur_reindex_continuous I.2.1).comp hf
  · intro z
    simpa only [Matrix.charpoly_reindex] using hsep z
  · intro z w
    simpa only [Matrix.charpoly_reindex] using hpoly z w

/-- Restricting to genuine scalar/nonreal-pair blocks still covers
every simple real matrix. -/
theorem realMatrix_mem_finiteAtomicSchurUnion
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hsep : A.charpoly.Separable) :
    A ∈ ⋃ I : RealSchurFiniteCode n, realSchurFiniteAtomicClass I := by
  obtain ⟨l,hl,e,Q,T,hT,hAtomic,hA⟩ := realMatrix_exists_reindexed_atomic_blocks A
  let s := realSchurListBlockSize l
  have hs : ∀ i, s i=1 ∨ s i=2 := fun i => hl _ (realSchurListBlockSize_mem l i)
  have hsum : (∑ i, s i)=n := by
    have hcard := Fintype.card_congr e
    simpa only [Fintype.card_sigma,Fintype.card_fin] using hcard.symm
  let S := RealSchurFiniteShape.ofSizes s hs hsum
  let I : RealSchurFiniteCode n := ⟨S,e,realSchurMixedSpectralCode s T⟩
  have hTsep : T.charpoly.Separable := by
    have hcp := congrArg Matrix.charpoly hA
    rw [Matrix.charpoly_reindex,realMatrixOrthogonalConjugation_charpoly _ _ _ Q.property] at hcp
    exact hcp ▸ hsep
  apply Set.mem_iUnion_of_mem I
  apply (realSchurAtomicCodeClass_mem_iff S.sizes S.sizes_pos I.2.2 _).mpr
  exact ⟨Q,T,hT,hTsep,rfl,hAtomic,hA⟩

theorem iUnion_realSchurFiniteAtomicClass (n : ℕ) :
    (⋃ I : RealSchurFiniteCode n, realSchurFiniteAtomicClass I) =
      {A : Matrix (Fin n) (Fin n) ℝ | A.charpoly.Separable} := by
  ext A
  constructor
  · intro hA
    obtain ⟨I,hI⟩ := Set.mem_iUnion.mp hA
    exact realSchurFiniteCodeClass_separable I A hI.1
  · exact realMatrix_mem_finiteAtomicSchurUnion A

#print axioms measurableSet_realSchurFiniteAtomicClass
#print axioms realSchurFiniteAtomicClass_connected_iff
#print axioms realMatrix_mem_finiteAtomicSchurUnion
#print axioms iUnion_realSchurFiniteAtomicClass
end SpectralRadiusUpperTail
