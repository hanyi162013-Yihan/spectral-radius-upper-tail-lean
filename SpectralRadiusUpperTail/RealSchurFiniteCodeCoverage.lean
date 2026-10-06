import SpectralRadiusUpperTail.RealSchurFiniteCodeClass
import SpectralRadiusUpperTail.RealSchurFixedMatrixRegularFrame

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator BigOperators

/-- All simple real matrices belong to the finite union of shape/code
classes. This is global coverage, with no local-chart source restriction. -/
theorem realMatrix_mem_finiteSchurCodeUnion
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hsep : A.charpoly.Separable) :
    A ∈ ⋃ I : RealSchurFiniteCode n, realSchurFiniteCodeClass I := by
  obtain ⟨l,hl,e,C,hA⟩ := realMatrix_exists_reindexed_regular_frame_of_separable A hsep
  let s := realSchurListBlockSize l
  have hs : ∀ i, s i=1 ∨ s i=2 :=
    fun i => hl _ (realSchurListBlockSize_mem l i)
  have hsum : (∑ i, s i)=n := by
    have hcard := Fintype.card_congr e
    simpa only [Fintype.card_sigma,Fintype.card_fin] using hcard.symm
  let S := RealSchurFiniteShape.ofSizes s hs hsum
  have hTsep : C.T.charpoly.Separable := by
    have hcp : (Matrix.reindex e e A).charpoly=C.T.charpoly := by
      rw [hA,realMatrixOrthogonalConjugation_charpoly _ _ _ C.orthogonal]
    rw [Matrix.charpoly_reindex] at hcp
    exact hcp ▸ hsep
  let I : RealSchurFiniteCode n := ⟨S,e,realSchurMixedSpectralCode s C.T⟩
  apply Set.mem_iUnion_of_mem I
  exact ⟨⟨C.Q,C.orthogonal⟩,C.T,C.upper,hTsep,rfl,hA⟩

/-- Conversely, every covered matrix has simple characteristic
polynomial, because simplicity is part of the intrinsic code class. -/
theorem realSchurFiniteCodeClass_separable
    {n : ℕ} (I : RealSchurFiniteCode n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ realSchurFiniteCodeClass I) : A.charpoly.Separable := by
  obtain ⟨Q,T,hT,hsep,hcode,hrep⟩ := hA
  have hcp := congrArg Matrix.charpoly hrep
  rw [Matrix.charpoly_reindex,realMatrixOrthogonalConjugation_charpoly _ _ _ Q.property] at hcp
  exact hcp.symm ▸ hsep

theorem iUnion_realSchurFiniteCodeClass (n : ℕ) :
    (⋃ I : RealSchurFiniteCode n, realSchurFiniteCodeClass I) =
      {A : Matrix (Fin n) (Fin n) ℝ | A.charpoly.Separable} := by
  ext A
  constructor
  · intro hA
    obtain ⟨I,hI⟩ := Set.mem_iUnion.mp hA
    exact realSchurFiniteCodeClass_separable I A hI
  · exact realMatrix_mem_finiteSchurCodeUnion A

#print axioms realMatrix_mem_finiteSchurCodeUnion
#print axioms realSchurFiniteCodeClass_separable
#print axioms iUnion_realSchurFiniteCodeClass
end SpectralRadiusUpperTail
