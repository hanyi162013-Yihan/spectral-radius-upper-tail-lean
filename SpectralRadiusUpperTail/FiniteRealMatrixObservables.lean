import SpectralRadiusUpperTail.FiniteCoordinateMatrixSpectrum
import SpectralRadiusUpperTail.SpectralMeasurable
import SpectralRadiusUpperTail.RealSchurMixedChartSpectrum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix Matrix.Norms.Frobenius ENNReal NNReal

local instance finiteObservableMatrixMeasurableSpace (ι : Type*) : MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

local instance finiteObservableMatrixBorelSpace (ι : Type*) [Fintype ι] : BorelSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (BorelSpace (ι → ι → ℝ))

noncomputable def finiteRealMatrixRadius {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ℝ := (spectralRadius ℂ (A.map Complex.ofRealHom)).toReal

theorem finiteRealMatrixRadius_eq_of_charpoly {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (h : A.charpoly=B.charpoly) :
    finiteRealMatrixRadius A=finiteRealMatrixRadius B := by
  have hh := real_matrix_radius_eq_of_zero_padded_charpoly B A 0
    (by simpa only [pow_zero,one_mul] using h)
  exact congrArg ENNReal.toReal hh

theorem finiteRealMatrixRadius_measurable {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (finiteRealMatrixRadius (ι := ι)) := by
  let e := Fintype.equivFin ι
  have he (A : Matrix ι ι ℝ) : finiteRealMatrixRadius A=
      realMatrixRadius (Matrix.reindex e e A) :=
    finiteRealMatrixRadius_eq_of_charpoly A (Matrix.reindex e e A)
      (Matrix.charpoly_reindex e A).symm
  have heq : finiteRealMatrixRadius (ι := ι)=(fun A => realMatrixRadius (Matrix.reindex e e A)) := funext he
  rw [heq]
  exact realMatrixRadius_measurable.comp (show Measurable (Matrix.reindex e e) by fun_prop)

theorem finiteRealMatrixRadius_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W A : Matrix ι ι ℝ) (hW : Wᵀ*W=1) (c : ℝ) :
    finiteRealMatrixRadius (c • (W*A*Wᵀ))=finiteRealMatrixRadius (c • A) := by
  have he : c • (W*A*Wᵀ)=W*(c • A)*Wᵀ := by
    simp only [Matrix.mul_smul,Matrix.smul_mul]
  rw [he]
  exact finiteRealMatrixRadius_eq_of_charpoly _ _
    (realMatrixOrthogonalConjugation_charpoly ι W (c • A) hW)

theorem finiteRealMatrixPower_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W A : Matrix ι ι ℝ) (hW : Wᵀ*W=1) (c : ℝ) (k : ℕ) (hk : 0 < k) :
    ‖(c • (W*A*Wᵀ))^k‖^2=‖(c • A)^k‖^2 := by
  have he : c • (W*A*Wᵀ)=W*(c • A)*Wᵀ := by
    simp only [Matrix.mul_smul,Matrix.smul_mul]
  rw [he]
  exact rectangular_isometry_conjugation_power_norm_sq W hW (c • A) k hk

#print axioms finiteRealMatrixRadius_eq_of_charpoly
#print axioms finiteRealMatrixRadius_measurable
#print axioms finiteRealMatrixRadius_conjugation
#print axioms finiteRealMatrixPower_conjugation
end SpectralRadiusUpperTail
