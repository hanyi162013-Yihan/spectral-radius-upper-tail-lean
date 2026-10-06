import SpectralRadiusUpperTail.TwoCoordinateSquareExp

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The sharp planar MGF condition includes finiteness of every expectation.
A Bochner integral inequality alone would not express this condition. -/
def SharpPlanarMGF (μ : Measure ℂ) : Prop :=
  ∀ u : ℂ, Integrable (fun z => Real.exp (2*(star u*z).re)) μ ∧
    (∫ z, Real.exp (2*(star u*z).re) ∂μ) ≤ Real.exp (‖u‖^2)

/-- The planar hypothesis controls either coordinate without assuming their
independence. -/
lemma sharp_planar_coordinate_mgf (μ : Measure ℂ) (h : SharpPlanarMGF μ) (t : ℝ) :
    (Integrable (fun z : ℂ => Real.exp (t*z.re)) μ ∧
      (∫ z : ℂ, Real.exp (t*z.re) ∂μ) ≤ Real.exp ((1/4)*t^2)) ∧
    (Integrable (fun z : ℂ => Real.exp (t*z.im)) μ ∧
      (∫ z : ℂ, Real.exp (t*z.im) ∂μ) ≤ Real.exp ((1/4)*t^2)) := by
  have hr := h ((t/2 : ℝ) : ℂ)
  have hi := h (((t/2 : ℝ) : ℂ)*Complex.I)
  have er (z : ℂ) : 2*(star ((t/2 : ℝ) : ℂ)*z).re = t*z.re := by
    simp [Complex.mul_re]
    ring
  have ei (z : ℂ) : 2*(star (((t/2 : ℝ) : ℂ)*Complex.I)*z).re = t*z.im := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have nr : ‖((t/2 : ℝ) : ℂ)‖^2 = (1/4)*t^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq]
    ring
  have ni : ‖(((t/2 : ℝ) : ℂ)*Complex.I)‖^2 = (1/4)*t^2 := by
    rw [norm_mul, Complex.norm_I, mul_one, nr]
  simp_rw [er, nr] at hr
  simp_rw [ei, ni] at hi
  exact ⟨hr, hi⟩

/-- A concrete square-exponential moment follows from the sharp planar MGF,
so it need not be imposed separately in the matching-class theorem. -/
theorem sharp_planar_squareExp (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h : SharpPlanarMGF μ) :
    Integrable (fun z : ℂ => Real.exp ((1/25)*‖z‖^2)) μ ∧
      (∫ z : ℂ, Real.exp ((1/25)*‖z‖^2) ∂μ) ≤ 2 := by
  have hr := quadratic_mgf_squareExp μ Complex.re Complex.continuous_re.measurable
    (1/4) (by norm_num) (fun t => (sharp_planar_coordinate_mgf μ h t).1)
  have hi := quadratic_mgf_squareExp μ Complex.im Complex.continuous_im.measurable
    (1/4) (by norm_num) (fun t => (sharp_planar_coordinate_mgf μ h t).2)
  norm_num at hr hi
  have hh := two_coordinate_squareExp μ (fun z : ℂ => z)
    aestronglyMeasurable_id (2/25) hr.1 hi.1 hr.2 hi.2
  norm_num at hh ⊢
  exact hh

#print axioms sharp_planar_coordinate_mgf
#print axioms sharp_planar_squareExp
end SpectralRadiusUpperTail
