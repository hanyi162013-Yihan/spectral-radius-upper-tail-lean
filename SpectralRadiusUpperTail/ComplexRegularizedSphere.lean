import SpectralRadiusUpperTail.ComplexSphereQuadraticBound
import SpectralRadiusUpperTail.MatrixQuadraticShift

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal MatrixOrder ComplexOrder Matrix.Norms.L2Operator

lemma complex_regularized_sphere_bound (n : ℕ) (hn : 0 < n)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef)
    (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    (∫⁻ v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1,
      ENNReal.ofReal (Real.exp (-c*(inner ℂ v.val (Matrix.toEuclideanCLM (𝕜 := ℂ) H v.val)).re))
      ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))) ≤
        ENNReal.ofReal (Real.exp (c*s)*(n.factorial : ℝ)/
          (c^n*‖(H+(s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖)) := by
  let J := (c : ℂ) • (H+(s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
  have hJ : J.PosDef := (matrix_regularized_posDef H hH s hs).smul
    (by exact_mod_cast hc : (0 : ℂ) < (c : ℂ))
  have hh := complex_sphere_quadratic_bound n hn J hJ.posSemidef (ne_of_gt hJ.det_pos)
  have he (v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1) :
      ENNReal.ofReal (Real.exp (-c*(inner ℂ v.val (Matrix.toEuclideanCLM (𝕜 := ℂ) H v.val)).re)) =
        ENNReal.ofReal (Real.exp (c*s))*
          ENNReal.ofReal (Real.exp (-(inner ℂ v.val (Matrix.toEuclideanCLM (𝕜 := ℂ) J v.val)).re)) := by
    have hv : ‖v.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
    congr 2
    rw [show (inner ℂ v.val (Matrix.toEuclideanCLM (𝕜 := ℂ) J v.val)).re =
        c*((inner ℂ v.val (Matrix.toEuclideanCLM (𝕜 := ℂ) H v.val)).re+s*‖v.val‖^2) from
      matrix_quadratic_scale_shift H c s v.val,hv]
    ring
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop)]
  apply (mul_le_mul' le_rfl hh).trans_eq
  dsimp only [J]
  rw [Matrix.det_smul,Fintype.card_fin,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  ring

#print axioms complex_regularized_sphere_bound
end SpectralRadiusUpperTail
