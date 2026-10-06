import SpectralRadiusUpperTail.RealOrthogonalCompact
import SpectralRadiusUpperTail.RealSchurMixedFlagAtlas
import SpectralRadiusUpperTail.MonicDivisorLocalConstancy
import SpectralRadiusUpperTail.RealSchurMixedNativeDiagonal
import Mathlib.Topology.Maps.Proper.Basic

namespace SpectralRadiusUpperTail
open Polynomial
open scoped Matrix Matrix.Norms.Operator

/-- Matrices admitting an orthogonal block-upper representation with a
specified ordered tuple of diagonal-block characteristic polynomials. -/
def realSchurMixedSpectralClass
    {m : ℕ} (s : Fin m → ℕ) (p : Fin m → ℝ[X]) :
    Set (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  {A | ∃ Q : RealSchurMixedOrthogonalFrame s,
    realSchurMixedLowerProjection s (Q.valᵀ*A*Q.val)=0 ∧
    ∀ a, (realSchurMixedDiagonalMatrix s (Q.valᵀ*A*Q.val) a).charpoly=p a}

/-- Prescribed Schur block polynomials survive limits. Compactness of
the orthogonal frames prevents the representing frames from escaping. -/
theorem isClosed_realSchurMixedSpectralClass
    {m : ℕ} (s : Fin m → ℕ) (p : Fin m → ℝ[X]) :
    IsClosed (realSchurMixedSpectralClass s p) := by
  let M := Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ
  let : CompactSpace (RealSchurMixedOrthogonalFrame s) :=
    isCompact_iff_compactSpace.mp (isCompact_realOrthogonalFrames _)
  let F : M × RealSchurMixedOrthogonalFrame s → M :=
    fun z => z.2.valᵀ*z.1*z.2.val
  have hF : Continuous F := by
    dsimp only [F]
    fun_prop
  let S : Set (M × RealSchurMixedOrthogonalFrame s) :=
    {z | realSchurMixedLowerProjection s (F z)=0} ∩
      ⋂ a, ⋂ t : ℝ,
        {z | (realSchurMixedDiagonalMatrix s (F z) a).charpoly.eval t=(p a).eval t}
  have hS : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_eq ((realSchurMixedLowerProjection s).continuous.comp hF)
        continuous_const
    · apply isClosed_iInter
      intro a
      apply isClosed_iInter
      intro t
      apply isClosed_eq _ continuous_const
      apply (realMatrix_charpoly_eval_continuous t).comp
      have hdiag : Continuous (fun A : M => realSchurMixedDiagonalMatrix s A a) := by
        unfold realSchurMixedDiagonalMatrix
        fun_prop
      exact hdiag.comp hF
  have heq : Prod.fst '' S = realSchurMixedSpectralClass s p := by
    ext A
    constructor
    · rintro ⟨⟨B,Q⟩,hB,rfl⟩
      refine ⟨Q,hB.1,?_⟩
      intro a
      apply Polynomial.funext
      intro t
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hB.2 a) t
    · rintro ⟨Q,hQ,hdiag⟩
      refine ⟨(A,Q),⟨hQ,?_⟩,rfl⟩
      apply Set.mem_iInter.mpr
      intro a
      apply Set.mem_iInter.mpr
      intro t
      change (realSchurMixedDiagonalMatrix s (Q.valᵀ*A*Q.val) a).charpoly.eval t = _
      rw [hdiag a]
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace S hS

#print axioms isClosed_realSchurMixedSpectralClass
end SpectralRadiusUpperTail
