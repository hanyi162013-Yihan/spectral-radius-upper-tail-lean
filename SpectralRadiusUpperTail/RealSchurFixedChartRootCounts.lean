import SpectralRadiusUpperTail.RealSchurFixedChartEntryTransport
import SpectralRadiusUpperTail.RealSchurMixedRegularCountIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- The original fixed-coordinate output of a mixed Schur chart. -/
noncomputable def realSchurFixedChartOutputEntries {n : ℕ}
    (c : RealSchurFixedChartIndex n)
    (t : RealSchurMixedTangent (realSchurListBlockSize c.shape)) :
    (Fin n × Fin n) → ℝ :=
  (realSchurFixedToMixedLinearEquiv c.indexEquiv).symm
    (realSchurMixedRotatedEntryCoordinates
      (realSchurListBlockSize c.shape) c.frame.T c.frame.Q
      c.frame.orthogonal t)

theorem realSchurFixedChartOutput_charpoly {n : ℕ}
    (c : RealSchurFixedChartIndex n)
    (t : RealSchurMixedTangent (realSchurListBlockSize c.shape)) :
    (Matrix.of (realSchurFixedChartOutputEntries c t).curry).charpoly =
      ((realSchurMixedEntryEquiv (realSchurListBlockSize c.shape)).symm
        (realSchurMixedRotatedEntryCoordinates
          (realSchurListBlockSize c.shape) c.frame.T c.frame.Q
          c.frame.orthogonal t)).charpoly := by
  let s := realSchurListBlockSize c.shape
  let y := realSchurMixedRotatedEntryCoordinates s c.frame.T c.frame.Q
    c.frame.orthogonal t
  let x := realSchurFixedChartOutputEntries c t
  have hE : realSchurMixedEntryEquiv s
      (Matrix.reindex c.indexEquiv c.indexEquiv
        (Matrix.of x.curry)) = y := by
    rw [← realSchurFixedToMixedTangent_eq_reindex c.indexEquiv x,
      ← realSchurFixedToMixedLinearEquiv_apply c.indexEquiv x]
    change (realSchurFixedToMixedLinearEquiv c.indexEquiv)
      ((realSchurFixedToMixedLinearEquiv c.indexEquiv).symm y) = y
    exact LinearEquiv.apply_symm_apply _ _
  have hM : Matrix.reindex c.indexEquiv c.indexEquiv
      (Matrix.of x.curry) = (realSchurMixedEntryEquiv s).symm y := by
    apply (realSchurMixedEntryEquiv s).injective
    simpa using hE
  calc
    (Matrix.of x.curry).charpoly =
        (Matrix.reindex c.indexEquiv c.indexEquiv
          (Matrix.of x.curry)).charpoly :=
      (Matrix.charpoly_reindex c.indexEquiv _).symm
    _ = ((realSchurMixedEntryEquiv s).symm y).charpoly := by
      rw [hM]

/-- At every fixed-coordinate chart output, a characteristic-root
count is exactly the sum of its diagonal block counts. -/
theorem realSchurFixedChartOutput_rootCountP {n : ℕ}
    (c : RealSchurFixedChartIndex n)
    (t : RealSchurMixedTangent (realSchurListBlockSize c.shape))
    (p : ℂ → Prop) [DecidablePred p] :
    Multiset.countP p
      ((Matrix.of (realSchurFixedChartOutputEntries c t).curry).charpoly.aroots ℂ) =
      ∑ i : Fin c.shape.length, Multiset.countP p
        (((c.frame.T+t.2.val).toSquareBlock
          (fun z : RealSchurMixedCoord (realSchurListBlockSize c.shape) => z.1)
          i).charpoly.aroots ℂ) := by
  rw [realSchurFixedChartOutput_charpoly]
  exact realSchurMixedRegularFrame_rotated_countP
    (realSchurListBlockSize c.shape) c.positive c.frame t p

#print axioms realSchurFixedChartOutput_rootCountP
end SpectralRadiusUpperTail
