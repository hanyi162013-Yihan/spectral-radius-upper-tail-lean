import SpectralRadiusUpperTail.RealSchurMixedOrbitDeterminant
import SpectralRadiusUpperTail.RealSchurSpectralGapFactors
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The coordinate matrix of `X ↦ D X - X E` on an arbitrary rectangular
bridge. -/
def realSchurRectangularSylvester {a b : ℕ}
    (D : Matrix (Fin a) (Fin a) ℝ)
    (E : Matrix (Fin b) (Fin b) ℝ) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℝ :=
  fun r z =>
    (if r.2=z.2 then D r.1 z.1 else 0) -
    (if r.1=z.1 then E z.2 r.2 else 0)

theorem realSchurMixedSylvester_eq_rectangular
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (D : ∀ i : Fin m, Matrix (Fin (s i)) (Fin (s i)) ℝ)
    (hD : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = D i a b)
    (p : RealSchurLowerIndex m) :
    realSchurMixedSylvester s T p =
      realSchurRectangularSylvester (D p.1.1) (D p.1.2) := by
  ext r z
  simp only [realSchurMixedSylvester, realSchurRectangularSylvester]
  rw [hD, hD]

/-- Two scalar blocks contribute their signed eigenvalue difference. -/
theorem realSchurRectangularSylvester_scalar_scalar (a u : ℝ) :
    (realSchurRectangularSylvester
      (Matrix.scalar (Fin 1) a) (Matrix.scalar (Fin 1) u)).det = a-u := by
  letI : Unique (Fin 1 × Fin 1) := {
    default := (0,0)
    uniq := by
      intro z
      rcases z with ⟨i,j⟩
      fin_cases i
      fin_cases j
      rfl }
  rw [Matrix.det_unique]
  simp [realSchurRectangularSylvester, Matrix.scalar]

/-- A pair below a scalar block contributes the quadratic spectral gap. -/
theorem realSchurRectangularSylvester_pair_scalar (a x b c : ℝ) :
    (realSchurRectangularSylvester
      (realSchurBlock x b c) (Matrix.scalar (Fin 1) a)).det =
      (x-a)^2+b*c := by
  let f : Fin 2 × Fin 1 ≃ Fin 2 :=
    (finProdFinEquiv : Fin 2 × Fin 1 ≃ Fin (2*1))
  have hM : Matrix.reindex f f
      (realSchurRectangularSylvester
        (realSchurBlock x b c) (Matrix.scalar (Fin 1) a)) =
        realSchurBlock x b c - Matrix.scalar (Fin 2) a := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [f, finProdFinEquiv, Fin.divNat, Fin.modNat,
        realSchurRectangularSylvester, realSchurBlock,
        Matrix.scalar, Matrix.sub_apply]
  calc
    _ = (Matrix.reindex f f
      (realSchurRectangularSylvester
        (realSchurBlock x b c) (Matrix.scalar (Fin 1) a))).det :=
      (Matrix.det_reindex_self f _).symm
    _ = (realSchurBlock x b c - Matrix.scalar (Fin 2) a).det :=
      congrArg Matrix.det hM
    _ = (x-a)^2+b*c := by
      simp [Matrix.det_fin_two, realSchurBlock, Matrix.scalar,
        Matrix.sub_apply]
      ring

/-- A scalar block below a pair gives the same positive quadratic gap. -/
theorem realSchurRectangularSylvester_scalar_pair (a x b c : ℝ) :
    (realSchurRectangularSylvester
      (Matrix.scalar (Fin 1) a) (realSchurBlock x b c)).det =
      (a-x)^2+b*c := by
  let f : Fin 1 × Fin 2 ≃ Fin 2 :=
    (finProdFinEquiv : Fin 1 × Fin 2 ≃ Fin (1*2))
  have hM : Matrix.reindex f f
      (realSchurRectangularSylvester
        (Matrix.scalar (Fin 1) a) (realSchurBlock x b c)) =
        (Matrix.scalar (Fin 2) a - realSchurBlock x b c)ᵀ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [f, finProdFinEquiv, Fin.divNat, Fin.modNat,
        realSchurRectangularSylvester, realSchurBlock,
        Matrix.scalar, Matrix.sub_apply, Matrix.transpose_apply]
  calc
    _ = (Matrix.reindex f f
      (realSchurRectangularSylvester
        (Matrix.scalar (Fin 1) a) (realSchurBlock x b c))).det :=
      (Matrix.det_reindex_self f _).symm
    _ = ((Matrix.scalar (Fin 2) a - realSchurBlock x b c)ᵀ).det :=
      congrArg Matrix.det hM
    _ = (a-x)^2+b*c := by
      rw [Matrix.det_transpose]
      simp [Matrix.det_fin_two, realSchurBlock, Matrix.scalar,
        Matrix.sub_apply]
      ring

/-- For two conjugate-pair blocks, the generic rectangular Sylvester
matrix is exactly the previously computed four-dimensional matrix. -/
theorem realSchurRectangularSylvester_pair_pair
    (x b c u d e : ℝ) :
    (realSchurRectangularSylvester
      (realSchurBlock x b c) (realSchurBlock u d e)).det =
      (realSchurPairPairSylvester x b c u d e).det := by
  let f : Fin 2 × Fin 2 ≃ Fin 4 :=
    (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2*2))
  have hM : Matrix.reindex f f
      (realSchurRectangularSylvester
        (realSchurBlock x b c) (realSchurBlock u d e)) =
        realSchurPairPairSylvester x b c u d e := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [f, finProdFinEquiv, Fin.divNat, Fin.modNat,
        realSchurRectangularSylvester, realSchurBlock,
        realSchurPairPairSylvester]
  calc
    _ = (Matrix.reindex f f
      (realSchurRectangularSylvester
        (realSchurBlock x b c) (realSchurBlock u d e))).det :=
      (Matrix.det_reindex_self f _).symm
    _ = _ := congrArg Matrix.det hM

#print axioms realSchurRectangularSylvester_pair_pair
end SpectralRadiusUpperTail
