import SpectralRadiusUpperTail.RealSchurAtomicDiagonalWeight
import SpectralRadiusUpperTail.RealSchurAtomicOrthogonalInvariance
import SpectralRadiusUpperTail.RealSchurBlockUpperConjugation

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator ENNReal

/-- The overlap correction in the diagonal integral does not depend on
the chosen angular frame or its chart index. -/
theorem realSchurAtomicDiagonalMultiplicityWeight_eq
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (d : RealSchurMixedDiagonalEntry I.1.sizes → ℝ) :
    realSchurAtomicDiagonalMultiplicityWeight F I k d =
      (realSchurAtomicMultiplicity n (Matrix.reindex I.2.1.symm I.2.1.symm
        (realSchurMixedUpperEntryJoin I.1.sizes d 0)))⁻¹ := by
  let s := I.1.sizes
  let E := Matrix.reindexAlgEquiv ℝ ℝ I.2.1.symm
  let Q := (F.frames I k).val
  have hQt : E Qᵀ=(E Q)ᵀ := (Matrix.transpose_reindex I.2.1.symm I.2.1.symm Q).symm
  have hEQ : (E Q)ᵀ*E Q=1 := by
    rw [← hQt,← map_mul,(F.frames I k).property,map_one]
  have hp : realSchurFixedFlagFiberMatrix s I.2.1 (F.frames I k) d (0,0) =
      E (Q*realSchurMixedUpperEntryJoin s d 0*Qᵀ) := by
    simp [realSchurFixedFlagFiberMatrix,realSchurMixedExpCoordinates_eq_conjugation,
      realSchurMixedAngularFrame,realSchurMixedFiberPoint,E,Q]
    rfl
  unfold realSchurAtomicDiagonalMultiplicityWeight
  rw [hp,map_mul,map_mul,hQt,realSchurAtomicMultiplicity_conjugation n _ _ hEQ]
  rfl

theorem realSchurAtomicDiagonalMultiplicityWeight_conjugation
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (W : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ)
    (hW : Wᵀ*W=1)
    (hoff : ∀ i j : RealSchurMixedCoord I.1.sizes, i.1 ≠ j.1 → W i j=0)
    (d : RealSchurMixedDiagonalEntry I.1.sizes → ℝ) :
    realSchurAtomicDiagonalMultiplicityWeight F I k
      (realSchurMixedDiagonalConjugation I.1.sizes W d) =
        realSchurAtomicDiagonalMultiplicityWeight F I k d := by
  let E := Matrix.reindexAlgEquiv ℝ ℝ I.2.1.symm
  have hWt : E Wᵀ=(E W)ᵀ := (Matrix.transpose_reindex I.2.1.symm I.2.1.symm W).symm
  have hEW : (E W)ᵀ*E W=1 := by rw [← hWt,← map_mul,hW,map_one]
  rw [realSchurAtomicDiagonalMultiplicityWeight_eq,
    realSchurAtomicDiagonalMultiplicityWeight_eq,
    realSchurMixedDiagonalConjugation_embed I.1.sizes W hoff d]
  change (realSchurAtomicMultiplicity n (E (W*realSchurMixedUpperEntryJoin I.1.sizes d 0*Wᵀ)))⁻¹ = _
  rw [map_mul,map_mul,hWt,realSchurAtomicMultiplicity_conjugation n _ _ hEW]
  rfl

/-- Along a connected family with fixed simple global spectrum, the
diagonal overlap correction is constant. In particular it does not
bias the within-pair gap variables. -/
theorem realSchurAtomicDiagonalMultiplicityWeight_connected
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (d : X → RealSchurMixedDiagonalEntry I.1.sizes → ℝ) (hd : Continuous d)
    (hsep : ∀ x, (realSchurMixedUpperEntryJoin I.1.sizes (d x) 0).charpoly.Separable)
    (hpoly : ∀ x y, (realSchurMixedUpperEntryJoin I.1.sizes (d x) 0).charpoly=
      (realSchurMixedUpperEntryJoin I.1.sizes (d y) 0).charpoly)
    (x y : X) :
    realSchurAtomicDiagonalMultiplicityWeight F I k (d x)=
      realSchurAtomicDiagonalMultiplicityWeight F I k (d y) := by
  rw [realSchurAtomicDiagonalMultiplicityWeight_eq,realSchurAtomicDiagonalMultiplicityWeight_eq]
  congr 1
  apply realSchurAtomicMultiplicity_connected
    (fun z => Matrix.reindex I.2.1.symm I.2.1.symm (realSchurMixedUpperEntryJoin I.1.sizes (d z) 0))
  · exact (realSchur_reindex_continuous I.2.1.symm).comp
      ((realSchurMixedUpperEntryJoin_continuous I.1.sizes).comp (hd.prodMk continuous_const))
  · intro z
    simpa only [Matrix.charpoly_reindex] using hsep z
  · intro z w
    simpa only [Matrix.charpoly_reindex] using hpoly z w

#print axioms realSchurAtomicDiagonalMultiplicityWeight_eq
#print axioms realSchurAtomicDiagonalMultiplicityWeight_conjugation
#print axioms realSchurAtomicDiagonalMultiplicityWeight_connected
end SpectralRadiusUpperTail
