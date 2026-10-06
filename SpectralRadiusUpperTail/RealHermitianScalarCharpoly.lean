import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A real symmetric matrix with the characteristic polynomial of a
scalar matrix is that scalar matrix. This removes the artificial upper
parameters when a Schur chart is restricted to a flag-marker orbit. -/
theorem realHermitian_eq_scalar_of_charpoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (c : ℝ)
    (hpoly : A.charpoly = (Matrix.scalar ι c).charpoly) :
    A = Matrix.scalar ι c := by
  have he : ∀ i, hA.eigenvalues i = c := by
    intro i
    have hr := (Matrix.mem_spectrum_iff_isRoot_charpoly.mp
      (hA.eigenvalues_mem_spectrum_real i))
    rw [hpoly] at hr
    have hz : (hA.eigenvalues i-c)^(Fintype.card ι) = 0 := by
      simpa [Polynomial.IsRoot, Matrix.scalar_apply, Matrix.charpoly_diagonal] using hr
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
  have hd : Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) =
      algebraMap ℝ (Matrix ι ι ℝ) c := by
    ext i j
    change (if i=j then hA.eigenvalues i else 0) = (if i=j then c else 0)
    simp only [he]
  calc
    A = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := hA.spectral_theorem
    _ = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (algebraMap ℝ (Matrix ι ι ℝ) c) := congrArg _ hd
    _ = algebraMap ℝ (Matrix ι ι ℝ) c :=
      (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary).toAlgEquiv.commutes c
    _ = Matrix.scalar ι c := rfl

#print axioms realHermitian_eq_scalar_of_charpoly
end SpectralRadiusUpperTail
