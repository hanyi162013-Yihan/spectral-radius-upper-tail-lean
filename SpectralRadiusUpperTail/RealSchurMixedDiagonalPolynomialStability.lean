import SpectralRadiusUpperTail.MonicDivisorLocalConstancy
import SpectralRadiusUpperTail.RealSchurMixedSpectralCode

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- Near a fixed upper matrix, its ordered block polynomials cannot
change while the global characteristic polynomial stays fixed. -/
theorem exists_open_realSchurMixed_diagonal_polynomial_stability
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    ∃ V : Set (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ),
      IsOpen V ∧ T ∈ V ∧
      ∀ U ∈ V, realSchurMixedLowerProjection s U=0 → U.charpoly=T.charpoly →
        ∀ a, (realSchurMixedDiagonalMatrix s U a).charpoly =
          (realSchurMixedDiagonalMatrix s T a).charpoly := by
  classical
  have hchoice (a : Fin m) := realPolynomial_monicDivisor_locally_constant
    (fun U : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ =>
      (realSchurMixedDiagonalMatrix s U a).charpoly)
    (fun t => (realMatrix_charpoly_eval_continuous t).comp
      (by unfold realSchurMixedDiagonalMatrix; fun_prop :
        Continuous (fun U => realSchurMixedDiagonalMatrix s U a)))
    T.charpoly (Matrix.charpoly_monic T).ne_zero T
  choose V hVo hVmem hVeq using hchoice
  refine ⟨⋂ a, V a, isOpen_iInter_of_finite hVo, Set.mem_iInter.mpr hVmem, ?_⟩
  intro U hU hLower hpoly a
  apply hVeq a U (Set.mem_iInter.mp hU a) (Matrix.charpoly_monic _)
  rw [← hpoly]
  exact realSchurMixedDiagonalMatrix_charpoly_dvd s hs U hLower a

#print axioms exists_open_realSchurMixed_diagonal_polynomial_stability
end SpectralRadiusUpperTail
