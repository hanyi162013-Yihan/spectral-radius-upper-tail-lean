import SpectralRadiusUpperTail.RealGaussianAtomicNormalization

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator ENNReal

theorem realSchurAtomicCodeClass_conjugation_mem
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (Q A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hQ : Qᵀ*Q=1) (hA : A ∈ realSchurAtomicCodeClass s code) :
    Q*A*Qᵀ ∈ realSchurAtomicCodeClass s code := by
  obtain ⟨P,T,hT,hsep,hcode,hAtomic,hrep⟩ :=
    (realSchurAtomicCodeClass_mem_iff s hs code A).mp hA
  have hQP : (Q*P.val)ᵀ*(Q*P.val)=1 := by
    calc
      _ = P.valᵀ*(Qᵀ*Q)*P.val := by simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _ = 1 := by rw [hQ,Matrix.mul_one,P.property]
  apply (realSchurAtomicCodeClass_mem_iff s hs code _).mpr
  refine ⟨⟨Q*P.val,hQP⟩,T,hT,hsep,hcode,hAtomic,?_⟩
  rw [hrep]
  simp only [Matrix.transpose_mul,Matrix.mul_assoc]

theorem realSchurAtomicCodeClass_conjugation_iff
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (Q A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hQ : Qᵀ*Q=1) :
    Q*A*Qᵀ ∈ realSchurAtomicCodeClass s code ↔ A ∈ realSchurAtomicCodeClass s code := by
  constructor
  · intro h
    have hQt : Qᵀᵀ*Qᵀ=1 := by simpa only [Matrix.transpose_transpose] using mul_eq_one_comm.mp hQ
    have hh := realSchurAtomicCodeClass_conjugation_mem s hs code Qᵀ (Q*A*Qᵀ) hQt h
    have heq : Qᵀ*(Q*A*Qᵀ)*Qᵀᵀ=A := by
      calc
        _ = (Qᵀ*Q)*A*(Qᵀ*Q) := by simp only [Matrix.transpose_transpose,Matrix.mul_assoc]
        _ = A := by simp only [hQ,Matrix.one_mul,Matrix.mul_one]
    rwa [heq] at hh
  · exact realSchurAtomicCodeClass_conjugation_mem s hs code Q A hQ

theorem realSchurFiniteAtomicClass_conjugation_iff
    {n : ℕ} (I : RealSchurFiniteCode n) (Q A : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ*Q=1) :
    Q*A*Qᵀ ∈ realSchurFiniteAtomicClass I ↔ A ∈ realSchurFiniteAtomicClass I := by
  let E := Matrix.reindexAlgEquiv ℝ ℝ I.2.1
  have hEt : E Qᵀ=(E Q)ᵀ := (Matrix.transpose_reindex I.2.1 I.2.1 Q).symm
  have hEQ : (E Q)ᵀ*E Q=1 := by
    rw [← hEt,← map_mul,hQ,map_one]
  change E (Q*A*Qᵀ) ∈ realSchurAtomicCodeClass I.1.sizes I.2.2 ↔
    E A ∈ realSchurAtomicCodeClass I.1.sizes I.2.2
  rw [map_mul,map_mul,hEt]
  exact realSchurAtomicCodeClass_conjugation_iff I.1.sizes I.1.sizes_pos I.2.2 (E Q) (E A) hEQ

/-- The exact finite overlap correction is orthogonally invariant,
including reflections. It introduces no angular bias in any block. -/
theorem realSchurAtomicMultiplicity_conjugation
    (n : ℕ) (Q A : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ*Q=1) :
    realSchurAtomicMultiplicity n (Q*A*Qᵀ)=realSchurAtomicMultiplicity n A := by
  classical
  apply Finset.sum_congr rfl
  intro I _
  simp only [Set.indicator_apply,realSchurFiniteAtomicClass_conjugation_iff I Q A hQ]

#print axioms realSchurAtomicCodeClass_conjugation_mem
#print axioms realSchurAtomicCodeClass_conjugation_iff
#print axioms realSchurFiniteAtomicClass_conjugation_iff
#print axioms realSchurAtomicMultiplicity_conjugation
end SpectralRadiusUpperTail
