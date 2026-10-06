import SpectralRadiusUpperTail.MarkedRealRankFiberConst
import SpectralRadiusUpperTail.RealMatrixRootRankSelector
import SpectralRadiusUpperTail.RealMatrixSimpleSpectrumOpen
import SpectralRadiusUpperTail.MarkedRealGaussianCoordinateTransport
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped Matrix

instance markedRealUpperMatrixMeasurableSpace (m : ℕ) :
    MeasurableSpace (Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ) :=
  borel _

instance markedRealUpperMatrixBorelSpace (m : ℕ) :
    BorelSpace (Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ) := ⟨rfl⟩

instance markedRealUpperSubmoduleMeasurableSpace (m : ℕ) :
    MeasurableSpace (realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m)) :=
  borel _

instance markedRealUpperSubmoduleBorelSpace (m : ℕ) :
    BorelSpace (realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m)) := ⟨rfl⟩

private theorem measurable_markedRealUpper_entry (m : ℕ)
    (i j : RealSchurMixedCoord (markedRealTwoBlockSizes m)) :
    Measurable (fun S : realSchurMixedUpperSubmodule
      (markedRealTwoBlockSizes m) => S.val i j) := by
  have hentry : Continuous
      (fun A : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
        (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ => A i j) := by
    fun_prop
  exact hentry.measurable.comp continuous_subtype_val.measurable

/-- Ordinary `Fin (m+1)` entries of the marked block-upper matrix. -/
noncomputable def markedRealUpperFlat (m : ℕ)
    (S : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m)) :
    (Fin (m+1) × Fin (m+1)) → ℝ :=
  fun ij => S.val (markedRealIndexEquiv m ij.1)
    (markedRealIndexEquiv m ij.2)

theorem markedRealUpperFlat_measurable (m : ℕ) :
    Measurable (markedRealUpperFlat m) := by
  unfold markedRealUpperFlat
  apply measurable_pi_lambda
  intro ij
  exact measurable_markedRealUpper_entry m _ _

theorem markedRealUpperFlat_charpoly
    (m : ℕ)
    (S : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m)) :
    (Matrix.of (markedRealUpperFlat m S).curry).charpoly =
      S.val.charpoly := by
  have hmatrix : Matrix.of (markedRealUpperFlat m S).curry =
      Matrix.reindex (markedRealIndexEquiv m).symm
        (markedRealIndexEquiv m).symm S.val := by
    ext i j
    rfl
  rw [hmatrix, Matrix.charpoly_reindex]

/-- Every real-root rank layer is Borel measurable, so the direct
rank-layer area formula can be applied to the whole product source. -/
theorem measurableSet_markedRealUpperRankSource
    (m k : ℕ) (b : ℝ) :
    MeasurableSet (markedRealUpperRankSource m k b) := by
  let F : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m) →
      (((Fin (m+1) × Fin (m+1)) → ℝ) × ℝ) :=
    fun S => (markedRealUpperFlat m S, markedRealScalar m S.val)
  have hscalar : Measurable
      (fun S : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m) =>
        markedRealScalar m S.val) := by
    exact measurable_markedRealUpper_entry m _ _
  have hF : Measurable F :=
    (markedRealUpperFlat_measurable m).prodMk hscalar
  have hsep : MeasurableSet
      {S : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m) |
        S.val.charpoly.Separable} :=
    (isOpen_realMatrix_charpoly_separable
      (RealSchurMixedCoord (markedRealTwoBlockSizes m))).measurableSet.preimage
        continuous_subtype_val.measurable
  have hb : MeasurableSet
      {S : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m) |
        b < markedRealScalar m S.val} :=
    measurableSet_lt measurable_const hscalar
  have hrank : MeasurableSet
      {S : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m) |
        realMatrixRootRankSelector (m+1) (F S) = k} :=
    measurableSet_eq_fun
      ((realMatrixRootRankSelector_measurable (m+1)).comp hF)
      measurable_const
  have hset : markedRealUpperRankSource m k b =
      {S | S.val.charpoly.Separable} ∩
        {S | b < markedRealScalar m S.val} ∩
          {S | realMatrixRootRankSelector (m+1) (F S) = k} := by
    ext S
    by_cases hs : S.val.charpoly.Separable
    · have hflat : (Matrix.of (markedRealUpperFlat m S).curry).charpoly.Separable := by
        rw [markedRealUpperFlat_charpoly]
        exact hs
      have heq := realMatrixRootRankSelector_eq_of_separable
        (m+1) (markedRealUpperFlat m S) (markedRealScalar m S.val) hflat
      rw [markedRealUpperFlat_charpoly] at heq
      simp [markedRealUpperRankSource, F, hs, heq]
    · simp [markedRealUpperRankSource, hs]
  rw [hset]
  exact (hsep.inter hb).inter hrank

#print axioms measurableSet_markedRealUpperRankSource
end SpectralRadiusUpperTail
