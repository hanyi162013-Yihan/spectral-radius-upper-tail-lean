import SpectralRadiusUpperTail.MarkedRealGaussianNormalizedArea
import SpectralRadiusUpperTail.RealGaussianPositiveRootFiberCount
import SpectralRadiusUpperTail.RealGaussianActualSimpleSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- The marked-incidence count in the area formula is the positive-real
exterior eigenvalue count of the original iid Gaussian matrix. -/
theorem markedRealSimpleRootCount_eq_exteriorCount_of_separable
    (m : ℕ) (hm : 0 < m) (r : ℝ)
    (a : (Fin (m+1) × Fin (m+1)) → ℝ)
    (hsep : (Matrix.of a.curry).charpoly.Separable) :
    markedRealSimpleRootCount m (r * Real.sqrt ((m+1 : ℕ) : ℝ))
      (Matrix.reindex (markedRealIndexEquiv m)
        (markedRealIndexEquiv m) (Matrix.of a.curry)) =
      ENNReal.ofReal (realGaussianExteriorCount (m+1) r 0 a) := by
  let A := Matrix.of a.curry
  let e := markedRealIndexEquiv m
  let s : Set ℝ := {x | A.charpoly.IsRoot x ∧
    r * Real.sqrt ((m+1 : ℕ) : ℝ) < x}
  have hfinite : s.Finite := by
    apply (Polynomial.finite_setOfPred_isRoot A.charpoly_monic.ne_zero).subset
    intro x hx
    exact hx.1
  have hchar : (Matrix.reindex e e A).charpoly = A.charpoly :=
    Matrix.charpoly_reindex e A
  have hcount := realGaussianExteriorCount_positive_eq_rootFiberNcard
    (m+1) (by omega) r a hsep
  have hcount' : realGaussianExteriorCount (m+1) r 0 a =
      (s.ncard : ℝ) := by
    simpa only [s, A] using hcount
  change ({x : ℝ |
      (Matrix.reindex e e A).charpoly.Separable ∧
        (Matrix.reindex e e A).charpoly.IsRoot x ∧
          r * Real.sqrt ((m+1 : ℕ) : ℝ) < x}.encard : ℝ≥0∞) = _
  rw [hchar]
  have hset : {x : ℝ | A.charpoly.Separable ∧ A.charpoly.IsRoot x ∧
      r * Real.sqrt ((m+1 : ℕ) : ℝ) < x} = s := by
    ext x
    have hsepA : A.charpoly.Separable := hsep
    simp [s, hsepA]
  rw [hset]
  rw [hcount', ENNReal.ofReal_natCast]
  exact_mod_cast hfinite.cast_ncard_eq.symm

theorem markedRealSimpleRootCount_eq_exteriorCount_ae
    (m : ℕ) (hm : 0 < m) (r : ℝ) :
    ∀ᵐ a ∂gaussianMatrixLaw (m+1),
      markedRealSimpleRootCount m (r * Real.sqrt ((m+1 : ℕ) : ℝ))
        (Matrix.reindex (markedRealIndexEquiv m)
          (markedRealIndexEquiv m) (Matrix.of a.curry)) =
        ENNReal.ofReal (realGaussianExteriorCount (m+1) r 0 a) := by
  filter_upwards [realGaussianMatrix_charpoly_separable_ae (m+1)] with a ha
  exact markedRealSimpleRootCount_eq_exteriorCount_of_separable m hm r a ha

#print axioms markedRealSimpleRootCount_eq_exteriorCount_ae
end SpectralRadiusUpperTail
