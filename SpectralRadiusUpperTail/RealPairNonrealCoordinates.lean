import SpectralRadiusUpperTail.RealSchurMixedResultantFactor
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Completing the square in the characteristic polynomial identifies
exactly the positive squared imaginary part of a nonreal pair. -/
theorem realPair_charpoly_eval (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    A.charpoly.eval t = (t-realPairCenter A)^2+realPairHeightSq A := by
  rw [Matrix.charpoly_fin_two]
  simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
  unfold realPairHeightSq realPairCenter
  ring

theorem realPair_noRealRoot_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ t : ℝ, A.charpoly.eval t ≠ 0) ↔ 0 < realPairHeightSq A := by
  constructor
  · intro h
    by_contra hp
    have hn : 0 ≤ -realPairHeightSq A := neg_nonneg.mpr (le_of_not_gt hp)
    have hs := Real.sq_sqrt hn
    apply h (realPairCenter A+Real.sqrt (-realPairHeightSq A))
    rw [realPair_charpoly_eval]
    have heq : realPairCenter A+Real.sqrt (-realPairHeightSq A)-realPairCenter A =
        Real.sqrt (-realPairHeightSq A) := by ring
    rw [heq,hs]
    ring
  · intro h t
    rw [realPair_charpoly_eval]
    exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) h)

/-- Trace, symmetric traceless coordinates, and the skew coordinate
parametrize every real two-dimensional block without an angular choice. -/
def realPairCartesianMatrix (x a p q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x+a,p+q;p-q,x-a]

theorem realPairCartesianMatrix_center (x a p q : ℝ) :
    realPairCenter (realPairCartesianMatrix x a p q)=x := by
  simp [realPairCenter,realPairCartesianMatrix,Matrix.trace_fin_two]

theorem realPairCartesianMatrix_heightSq (x a p q : ℝ) :
    realPairHeightSq (realPairCartesianMatrix x a p q)=q^2-a^2-p^2 := by
  rw [realPairHeightSq,realPairCartesianMatrix_center]
  simp [realPairCartesianMatrix,Matrix.det_fin_two]
  ring

theorem realPairCartesianMatrix_energy (x a p q : ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, (realPairCartesianMatrix x a p q i j)^2) =
      2*(x^2+a^2+p^2+q^2) := by
  simp [realPairCartesianMatrix,Fin.sum_univ_two]
  ring

theorem realPairCartesianMatrix_reconstruct (A : Matrix (Fin 2) (Fin 2) ℝ) :
    realPairCartesianMatrix ((A 0 0+A 1 1)/2) ((A 0 0-A 1 1)/2)
      ((A 0 1+A 1 0)/2) ((A 0 1-A 1 0)/2)=A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realPairCartesianMatrix] <;> ring

#print axioms realPair_charpoly_eval
#print axioms realPair_noRealRoot_iff
#print axioms realPairCartesianMatrix_center
#print axioms realPairCartesianMatrix_heightSq
#print axioms realPairCartesianMatrix_energy
#print axioms realPairCartesianMatrix_reconstruct
end SpectralRadiusUpperTail
