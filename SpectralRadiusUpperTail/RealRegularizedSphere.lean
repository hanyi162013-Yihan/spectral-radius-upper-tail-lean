import SpectralRadiusUpperTail.RealSphereQuadraticBound
import SpectralRadiusUpperTail.MatrixQuadraticShift

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal MatrixOrder ComplexOrder Matrix.Norms.L2Operator

lemma real_regularized_sphere_bound (n : ℕ) (hn : 0 < n)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosSemidef)
    (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    (∫⁻ v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      ENNReal.ofReal (Real.exp (-c*(inner ℝ v.val (Matrix.toEuclideanCLM (𝕜 := ℝ) H v.val))))
      ∂haarSphereProbability (volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ENNReal.ofReal (Real.exp (c*s)*Real.Gamma ((n : ℝ)/2+1)/
          Real.sqrt (c^n*|(H+(s : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).det|)) := by
  let J := (c : ℝ) • (H+(s : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
  have hJ : J.PosDef := (matrix_regularized_posDef H hH s hs).smul
    (by exact_mod_cast hc : (0 : ℝ) < (c : ℝ))
  have hh := real_sphere_quadratic_bound n hn J hJ.posSemidef (ne_of_gt hJ.det_pos)
  have he (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      ENNReal.ofReal (Real.exp (-c*(inner ℝ v.val (Matrix.toEuclideanCLM (𝕜 := ℝ) H v.val)))) =
        ENNReal.ofReal (Real.exp (c*s))*
          ENNReal.ofReal (Real.exp (-(inner ℝ v.val (Matrix.toEuclideanCLM (𝕜 := ℝ) J v.val)))) := by
    have hv : ‖v.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
    congr 2
    rw [show (inner ℝ v.val (Matrix.toEuclideanCLM (𝕜 := ℝ) J v.val)) =
        c*((inner ℝ v.val (Matrix.toEuclideanCLM (𝕜 := ℝ) H v.val))+s*‖v.val‖^2) from
      matrix_quadratic_scale_shift H c s v.val,hv]
    ring
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop)]
  apply (mul_le_mul' le_rfl hh).trans_eq
  dsimp only [J]
  rw [Matrix.det_smul,Fintype.card_fin,abs_mul,abs_pow,abs_of_pos hc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  ring

#print axioms real_regularized_sphere_bound
end SpectralRadiusUpperTail
