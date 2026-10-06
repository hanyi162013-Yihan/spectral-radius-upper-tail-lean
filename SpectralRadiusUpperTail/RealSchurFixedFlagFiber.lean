import SpectralRadiusUpperTail.RealSchurFiniteMultiplicity
import SpectralRadiusUpperTail.RealSchurMixedFlagGaussianIntegral
import SpectralRadiusUpperTail.RealSchurMixedCodeClassFiber

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- A fixed diagonal array, with arbitrary angle and strict-upper
entries, returned to the original matrix coordinates. -/
noncomputable def realSchurFixedFlagFiberMatrix
    {n m : ℕ} (s : Fin m → ℕ) (e : Fin n ≃ RealSchurMixedCoord s)
    (Q : RealSchurMixedOrthogonalFrame s) (d : RealSchurMixedDiagonalEntry s → ℝ)
    (z : (RealSchurMixedOrbitIndex s → ℝ) × (RealSchurMixedStrictUpperEntry s → ℝ)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.reindex e.symm e.symm (Q.val*
    realSchurMixedExpCoordinates s 0 (realSchurMixedFiberPoint s z.1 d z.2)*Q.valᵀ)

theorem realSchurFixedFlagFiberMatrix_continuous
    {n m : ℕ} (s : Fin m → ℕ) (e : Fin n ≃ RealSchurMixedCoord s)
    (Q : RealSchurMixedOrthogonalFrame s) (d : RealSchurMixedDiagonalEntry s → ℝ) :
    Continuous (realSchurFixedFlagFiberMatrix s e Q d) := by
  have hU : Continuous (fun z : (RealSchurMixedOrbitIndex s → ℝ) ×
      (RealSchurMixedStrictUpperEntry s → ℝ) =>
        (realSchurMixedUpperEntryEquiv s).symm (d,z.2)) :=
    (realSchurMixedUpperEntryEquiv s).symm.toContinuousLinearEquiv.continuous.comp
      (continuous_const.prodMk continuous_snd)
  have hF : Continuous (fun z : (RealSchurMixedOrbitIndex s → ℝ) ×
      (RealSchurMixedStrictUpperEntry s → ℝ) => realSchurMixedFiberPoint s z.1 d z.2) :=
    continuous_fst.prodMk hU
  have hE := (realSchurMixedExpCoordinates_contDiff s 0 1).continuous.comp hF
  exact (realSchur_reindex_continuous e.symm).comp ((continuous_const.mul hE).mul continuous_const)

theorem realSchurFixedFlagFiberMatrix_charpoly
    {n m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (e : Fin n ≃ RealSchurMixedCoord s) (Q : RealSchurMixedOrthogonalFrame s)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (z : (RealSchurMixedOrbitIndex s → ℝ) × (RealSchurMixedStrictUpperEntry s → ℝ)) :
    (realSchurFixedFlagFiberMatrix s e Q d z).charpoly =
      (realSchurMixedUpperEntryJoin s d 0).charpoly := by
  unfold realSchurFixedFlagFiberMatrix
  rw [Matrix.charpoly_reindex,realMatrixOrthogonalConjugation_charpoly _ _ _ Q.property,
    realSchurMixedExpCoordinates_eq_conjugation,
    realMatrixOrthogonalConjugation_charpoly _ _ _ (realSchurMixedAngularFrame_orthogonal s _),
    zero_add,realSchurMixedFiberPoint_upper]
  exact realSchurMixedUpperEntryJoin_charpoly_fiber_const s hs d z.2 0

/-- The total multiplicity, including every shape, is constant along
each full angular/strict-upper fiber. This is the normalization needed
before integrating its independent Gaussian entries. -/
theorem realSchurFiniteMultiplicity_flag_fiber
    {n m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (e : Fin n ≃ RealSchurMixedCoord s) (Q : RealSchurMixedOrthogonalFrame s)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (hsep : (realSchurMixedUpperEntryJoin s d 0).charpoly.Separable)
    (z w : (RealSchurMixedOrbitIndex s → ℝ) × (RealSchurMixedStrictUpperEntry s → ℝ)) :
    realSchurFiniteMultiplicity n (realSchurFixedFlagFiberMatrix s e Q d z) =
      realSchurFiniteMultiplicity n (realSchurFixedFlagFiberMatrix s e Q d w) := by
  apply realSchurFiniteMultiplicity_connected _ (realSchurFixedFlagFiberMatrix_continuous s e Q d)
  · intro v
    rw [realSchurFixedFlagFiberMatrix_charpoly s hs]
    exact hsep
  · intro v t
    rw [realSchurFixedFlagFiberMatrix_charpoly s hs,realSchurFixedFlagFiberMatrix_charpoly s hs]

#print axioms realSchurFixedFlagFiberMatrix_continuous
#print axioms realSchurFixedFlagFiberMatrix_charpoly
#print axioms realSchurFiniteMultiplicity_flag_fiber
end SpectralRadiusUpperTail
