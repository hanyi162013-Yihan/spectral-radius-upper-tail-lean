import SpectralRadiusUpperTail.MarkedRealDiagonalCharpolyFactor
import SpectralRadiusUpperTail.MarkedRealDiagonalGaussianIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal Matrix BigOperators

/-- The rank-free diagonal integrand in the explicit scalar/matrix
coordinates. The simple-spectrum guard is retained exactly. -/
noncomputable def markedRealExplicitDiagonalWeight
    (m : ℕ) (b : ℝ) (z : ℝ × ((Fin m × Fin m) → ℝ)) : ℝ≥0∞ :=
  let H : Matrix (Fin m) (Fin m) ℝ := Matrix.of z.2.curry
  if ((Polynomial.X - Polynomial.C z.1) * H.charpoly).Separable ∧
      b < z.1 then
    ENNReal.ofReal |(H - z.1 • (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
      (ENNReal.ofReal
        (Real.exp (-(z.1^2 + ∑ ij : Fin m × Fin m, (z.2 ij)^2)/2)) *
        ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
          (Fintype.card
            (RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m)))))
  else 0

theorem markedRealSimpleDiagonalWeight_explicit
    (m : ℕ) (hm : 0 < m) (b : ℝ)
    (z : ℝ × ((Fin m × Fin m) → ℝ)) :
    markedRealSimpleDiagonalWeight m b
      ((markedRealDiagonalProductEquiv m).symm z) =
        markedRealExplicitDiagonalWeight m b z := by
  let E := markedRealDiagonalProductEquiv m
  let d := E.symm z
  let s := markedRealTwoBlockSizes m
  let S₀ := (realSchurMixedUpperEntryEquiv s).symm
    (d, (0 : RealSchurMixedStrictUpperEntry s → ℝ))
  let H : Matrix (Fin m) (Fin m) ℝ := Matrix.of z.2.curry
  have hz : E d = z := E.apply_symm_apply z
  have hs : markedRealScalar m S₀.val = z.1 := by
    calc
      markedRealScalar m S₀.val = (E d).1 :=
        markedRealDiagonal_join_scalar m d 0
      _ = z.1 := congrArg Prod.fst hz
  have hc : markedRealComplement m S₀.val = H := by
    calc
      markedRealComplement m S₀.val =
          Matrix.of (E d).2.curry :=
        markedRealDiagonal_join_complement m d 0
      _ = H := by rw [hz]
  have he : (∑ p : RealSchurMixedDiagonalEntry s, (d p)^2) =
      z.1^2 + ∑ ij : Fin m × Fin m, (z.2 ij)^2 := by
    rw [markedRealDiagonal_energy_split]
    rw [hz]
  have hp : S₀.val.charpoly =
      (Polynomial.X - Polynomial.C z.1) * H.charpoly := by
    change (realSchurMixedUpperEntryJoin s d 0).charpoly = _
    rw [markedRealDiagonal_join_charpoly m hm d 0, hz]
  have hg : S₀ ∈ markedRealUpperSimpleSource m b ↔
      ((Polynomial.X - Polynomial.C z.1) * H.charpoly).Separable ∧
        b < z.1 := by
    change (S₀.val.charpoly.Separable ∧
      b < markedRealScalar m S₀.val) ↔ _
    rw [hp, hs]
  have hw :
      ENNReal.ofReal |(markedRealComplement m S₀.val -
        markedRealScalar m S₀.val •
          (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
        (ENNReal.ofReal
          (Real.exp (-(∑ p : RealSchurMixedDiagonalEntry s,
            (d p)^2)/2)) *
          ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
            (Fintype.card (RealSchurMixedStrictUpperEntry s)))) =
      ENNReal.ofReal |(H - z.1 •
          (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
        (ENNReal.ofReal
          (Real.exp (-(z.1^2 +
            ∑ ij : Fin m × Fin m, (z.2 ij)^2)/2)) *
          ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
            (Fintype.card (RealSchurMixedStrictUpperEntry s)))) := by
    rw [hc, hs, he]
  change (if S₀ ∈ markedRealUpperSimpleSource m b then
      ENNReal.ofReal |(markedRealComplement m S₀.val -
        markedRealScalar m S₀.val •
          (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
        (ENNReal.ofReal
          (Real.exp (-(∑ p : RealSchurMixedDiagonalEntry s,
            (d p)^2)/2)) *
          ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
            (Fintype.card (RealSchurMixedStrictUpperEntry s))))
      else 0) =
    (if ((Polynomial.X - Polynomial.C z.1) *
        H.charpoly).Separable ∧ b < z.1 then
      ENNReal.ofReal |(H - z.1 •
          (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
        (ENNReal.ofReal
          (Real.exp (-(z.1^2 +
            ∑ ij : Fin m × Fin m, (z.2 ij)^2)/2)) *
          ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
            (Fintype.card (RealSchurMixedStrictUpperEntry s))))
      else 0)
  rw [hg, hw]
  by_cases hG : ((Polynomial.X - Polynomial.C z.1) *
      H.charpoly).Separable ∧ b < z.1
  · simp only [if_pos hG]
  · simp only [if_neg hG]

#print axioms markedRealSimpleDiagonalWeight_explicit
end SpectralRadiusUpperTail
