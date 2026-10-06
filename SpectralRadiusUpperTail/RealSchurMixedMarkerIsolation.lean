import SpectralRadiusUpperTail.MonicDivisorLocalConstancy
import SpectralRadiusUpperTail.RealHermitianScalarCharpoly
import SpectralRadiusUpperTail.RealSchurMixedBlockScalar
import SpectralRadiusUpperTail.RealSchurMixedNativeDiagonal

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

theorem realSchurMixedBlockScalar_diagonalMatrix
    {m : ℕ} (s : Fin m → ℕ) (c : Fin m → ℝ) (i : Fin m) :
    realSchurMixedDiagonalMatrix s (realSchurMixedBlockScalar s c) i =
      Matrix.scalar (Fin (s i)) (c i) := by
  ext a b
  simp [realSchurMixedDiagonalMatrix, realSchurMixedBlockScalar,
    Matrix.scalar_apply, Matrix.diagonal_apply]

theorem realSchurMixed_hermitian_eq_blockScalar
    {m : ℕ} (s : Fin m → ℕ) (c : Fin m → ℝ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hHerm : T.IsHermitian) (hLower : realSchurMixedLowerProjection s T = 0)
    (hdiag : ∀ i, (realSchurMixedDiagonalMatrix s T i).charpoly =
      (Matrix.scalar (Fin (s i)) (c i)).charpoly) :
    T = realSchurMixedBlockScalar s c := by
  have hblock (i : Fin m) : realSchurMixedDiagonalMatrix s T i =
      Matrix.scalar (Fin (s i)) (c i) :=
    realHermitian_eq_scalar_of_charpoly _ (hHerm.submatrix (fun a => ⟨i,a⟩))
      (c i) (hdiag i)
  have hupper := (realSchurMixed_blockTriangular_iff_lower_zero s T).mpr hLower
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases hij : i=j
  · subst j
    change (realSchurMixedDiagonalMatrix s T i) a b =
      (realSchurMixedDiagonalMatrix s (realSchurMixedBlockScalar s c) i) a b
    rw [hblock i, realSchurMixedBlockScalar_diagonalMatrix]
  · have hzero : realSchurMixedBlockScalar s c ⟨i,a⟩ ⟨j,b⟩ = 0 := by
      simp [realSchurMixedBlockScalar, hij]
    rw [hzero]
    rcases lt_or_gt_of_ne hij with h | h
    · simpa only [star_trivial, hupper (i := ⟨j,b⟩) (j := ⟨i,a⟩) h] using
        hHerm.apply ⟨j,b⟩ ⟨i,a⟩
    · exact hupper h

/-- Near a block-scalar marker, its orthogonal orbit meets the symmetric
block-upper slice only at that marker. Finiteness of monic polynomial
divisors supplies the neighborhood without eigenvalue perturbation bounds. -/
theorem exists_open_realSchurMixed_marker_isolation
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i) (c : Fin m → ℝ) :
    ∃ V : Set (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ),
      IsOpen V ∧ realSchurMixedBlockScalar s c ∈ V ∧
      ∀ T ∈ V, T.IsHermitian → realSchurMixedLowerProjection s T = 0 →
        T.charpoly = (realSchurMixedBlockScalar s c).charpoly →
        T = realSchurMixedBlockScalar s c := by
  classical
  let D := realSchurMixedBlockScalar s c
  have hchoice (i : Fin m) := realPolynomial_monicDivisor_locally_constant
    (fun T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ =>
      (realSchurMixedDiagonalMatrix s T i).charpoly)
    (fun t => (realMatrix_charpoly_eval_continuous t).comp
      (by unfold realSchurMixedDiagonalMatrix; fun_prop :
        Continuous (fun T => realSchurMixedDiagonalMatrix s T i)))
    D.charpoly (Matrix.charpoly_monic D).ne_zero D
  choose V hVo hVmem hVisol using hchoice
  refine ⟨⋂ i, V i, isOpen_iInter_of_finite hVo, Set.mem_iInter.mpr hVmem, ?_⟩
  intro T hT hHerm hLower hpoly
  apply realSchurMixed_hermitian_eq_blockScalar s c T hHerm hLower
  intro i
  have hprod : T.charpoly = ∏ j : Fin m, (realSchurMixedDiagonalMatrix s T j).charpoly := by
    rw [realSchurMixed_blockUpper_charpoly s hs T hLower]
    simp_rw [realSchurMixedDiagonalMatrix_charpoly]
  have hdvd : (realSchurMixedDiagonalMatrix s T i).charpoly ∣ D.charpoly := by
    rw [← hpoly, hprod]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have heq := hVisol i T (Set.mem_iInter.mp hT i)
    (Matrix.charpoly_monic _) hdvd
  simpa only [D, realSchurMixedBlockScalar_diagonalMatrix] using heq

#print axioms realSchurMixedBlockScalar_diagonalMatrix
#print axioms realSchurMixed_hermitian_eq_blockScalar
#print axioms exists_open_realSchurMixed_marker_isolation
end SpectralRadiusUpperTail
