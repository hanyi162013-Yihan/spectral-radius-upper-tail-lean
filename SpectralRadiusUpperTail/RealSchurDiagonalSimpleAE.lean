import SpectralRadiusUpperTail.PolynomialMatrixSimpleAE
import SpectralRadiusUpperTail.RealSchurMixedUpperEntryCoordinates

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The unrestricted native diagonal blocks have simple combined spectrum
for almost every diagonal-entry array, for arbitrary block sizes. -/
theorem realSchurMixedDiagonal_simpleSpectrum_ae
    {m : ℕ} (s : Fin m → ℕ) :
    ∀ᵐ d : RealSchurMixedDiagonalEntry s → ℝ,
      (realSchurMixedUpperEntryJoin s d 0).charpoly.Separable := by
  let ι := RealSchurMixedCoord s
  let p : ι × ι → MvPolynomial (RealSchurMixedDiagonalEntry s) ℝ :=
    fun ij => if h : ij.1.1=ij.2.1 then MvPolynomial.X ⟨ij,h⟩ else 0
  have hp (d : RealSchurMixedDiagonalEntry s → ℝ) :
      Matrix.of (fun ij => MvPolynomial.eval d (p ij)).curry =
        realSchurMixedUpperEntryJoin s d 0 := by
    ext i j
    by_cases h : i.1=j.1 <;>
      simp [p,realSchurMixedUpperEntryJoin,h]
  obtain ⟨a,ha⟩ := finiteRealMatrix_diagonal_distinct_charpoly_separable ι
  let d : RealSchurMixedDiagonalEntry s → ℝ :=
    fun ij => Matrix.diagonal a ij.1.1 ij.1.2
  have hd : realSchurMixedUpperEntryJoin s d 0=Matrix.diagonal a := by
    ext i j
    by_cases h : i.1=j.1
    · simp [realSchurMixedUpperEntryJoin,h,d]
    · have hij : i ≠ j := fun he => h (congrArg Sigma.fst he)
      simp [realSchurMixedUpperEntryJoin,h,d,Matrix.diagonal_apply,hij]
  have h := polynomialMatrix_charpoly_separable_ae p d (by rw [hp,hd]; exact ha)
  filter_upwards [h] with d hd
  rwa [hp] at hd

#print axioms realSchurMixedDiagonal_simpleSpectrum_ae
end SpectralRadiusUpperTail
