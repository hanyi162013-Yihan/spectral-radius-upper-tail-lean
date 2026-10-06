import SpectralRadiusUpperTail.ExponentialVariation
import Mathlib.Probability.Moments.SubGaussian

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory

lemma exp_le_one_add_linear_quadratic (x : ℝ) :
    Real.exp x ≤ 1+x+x^2*Real.exp |x| := by
  have he : 1 ≤ Real.exp |x| := Real.one_le_exp_iff.mpr (abs_nonneg _)
  by_cases hx : |x| ≤ 1
  · have hh := (le_abs_self (Real.exp x-1-x)).trans
      (Real.abs_exp_sub_one_sub_id_le hx)
    have hp := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr he)
    nlinarith
  · have ha : 1 ≤ |x| := (lt_of_not_ge hx).le
    have hs : 1 ≤ x^2 := by nlinarith [sq_abs x]
    have hx2 : 0 ≤ x^2+x := by nlinarith [sq_abs x, neg_abs_le x]
    have hp := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr he)
    have he' : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
    nlinarith

lemma young_linear_square (t x τ : ℝ) (hτ : 0 < τ) :
    t*x ≤ τ*x^2+t^2/(4*τ) := by
  have hd : 0 < 4*τ := by positivity
  apply (mul_le_mul_iff_of_pos_right hd).mp
  have he : (τ*x^2+t^2/(4*τ))*(4*τ) = 4*τ^2*x^2+t^2 := by
    field_simp
  rw [he]
  nlinarith [sq_nonneg (2*τ*x-t)]

lemma norm_square_exp_linear_bound (r τ : ℝ) (hr : 0 ≤ r) (hτ : 0 < τ) :
    r^2*Real.exp r ≤ ((2/τ)*Real.exp (1/(2*τ)))*Real.exp (τ*r^2) := by
  have hp : r^2 ≤ (2/τ)*Real.exp (τ*r^2/2) := by
    have he := Real.add_one_le_exp (τ*r^2/2)
    calc
      _ ≤ (2*Real.exp (τ*r^2/2))/τ := (le_div_iff₀ hτ).mpr (by nlinarith)
      _ = _ := by ring
  have hy : r ≤ τ*r^2/2+1/(2*τ) := by
    have h := young_linear_square 1 r (τ/2) (by positivity)
    convert h using 1 <;> field_simp <;> ring
  have he : Real.exp r ≤ Real.exp (τ*r^2/2)*Real.exp (1/(2*τ)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hy
  have hh := mul_le_mul hp he (Real.exp_nonneg r) (by positivity)
  have hprod : Real.exp (τ*r^2/2)*Real.exp (τ*r^2/2) = Real.exp (τ*r^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ ((2/τ)*Real.exp (τ*r^2/2))*(Real.exp (τ*r^2/2)*Real.exp (1/(2*τ))) := hh
    _ = ((2/τ)*Real.exp (1/(2*τ)))*(Real.exp (τ*r^2/2)*Real.exp (τ*r^2/2)) := by ring
    _ = _ := by rw [hprod]

noncomputable def squareExpMgfConstant (τ M : ℝ) : ℝ :=
  ((2/τ)*Real.exp (1/(2*τ)))*M+M+1/(4*τ)

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- A centered real projection dominated by the entry norm has a quadratic MGF
bound with a constant independent of the projection. -/
theorem squareExp_projected_mgf (μ : Measure E) [IsProbabilityMeasure μ]
    (X : E → ℝ) (hX : Measurable X) (hXi : Integrable X μ)
    (hmean : (∫ x, X x ∂μ) = 0) (hbound : ∀ x, |X x| ≤ ‖x‖)
    (τ : ℝ) (hτ : 0 < τ)
    (hexp : Integrable (fun x : E => Real.exp (τ*‖x‖^2)) μ) (t : ℝ) :
    Integrable (fun x => Real.exp (t*X x)) μ ∧
      (∫ x, Real.exp (t*X x) ∂μ) ≤
        Real.exp (squareExpMgfConstant τ (∫ x : E, Real.exp (τ*‖x‖^2) ∂μ)*t^2) := by
  let M := ∫ x : E, Real.exp (τ*‖x‖^2) ∂μ
  let A := (2/τ)*Real.exp (1/(2*τ))
  have hM : 0 ≤ M := integral_nonneg (fun _ => Real.exp_nonneg _)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hxsq (x : E) : (X x)^2 ≤ ‖x‖^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (X x)) (hbound x) 2
    simpa only [sq_abs] using h
  have hy (x : E) : Real.exp (t*X x) ≤ Real.exp (t^2/(4*τ))*Real.exp (τ*‖x‖^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := young_linear_square t (X x) τ hτ
    have hs := mul_le_mul_of_nonneg_left (hxsq x) hτ.le
    linarith
  have hmexp : Measurable (fun x => Real.exp (t*X x)) :=
    Real.measurable_exp.comp (measurable_const.mul hX)
  have hi := (hexp.const_mul (Real.exp (t^2/(4*τ)))).mono_nonneg
    hmexp.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)) (Filter.Eventually.of_forall hy)
  refine ⟨hi, ?_⟩
  change (∫ x, Real.exp (t*X x) ∂μ) ≤ Real.exp (squareExpMgfConstant τ M*t^2)
  have hlarge : (∫ x, Real.exp (t*X x) ∂μ) ≤ Real.exp (t^2/(4*τ))*M := by
    have h := integral_mono hi (hexp.const_mul _) hy
    simpa only [integral_const_mul] using h
  by_cases ht : |t| ≤ 1
  · have he (x : E) : (X x)^2*Real.exp |t*X x| ≤ A*Real.exp (τ*‖x‖^2) := by
      have hb : |t*X x| ≤ ‖x‖ := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans (by simpa using hbound x)
      have hp := mul_le_mul (hxsq x) (Real.exp_le_exp.mpr hb)
        (Real.exp_nonneg _) (sq_nonneg _)
      exact hp.trans (norm_square_exp_linear_bound ‖x‖ τ (norm_nonneg _) hτ)
    have hb (x : E) : Real.exp (t*X x) ≤
        1+t*X x+(t^2*A)*Real.exp (τ*‖x‖^2) := by
      have h := exp_le_one_add_linear_quadratic (t*X x)
      have h' := mul_le_mul_of_nonneg_left (he x) (sq_nonneg t)
      nlinarith only [h, h']
    have hlin : Integrable (fun x => 1+t*X x) μ :=
      (integrable_const (1 : ℝ)).add (hXi.const_mul t)
    have htop : Integrable (fun x => 1+t*X x+(t^2*A)*Real.exp (τ*‖x‖^2)) μ :=
      hlin.add (hexp.const_mul (t^2*A))
    have hh := integral_mono hi htop hb
    have hm : (∫ x, 1+t*X x+(t^2*A)*Real.exp (τ*‖x‖^2) ∂μ) = 1+t^2*A*M := by
      rw [integral_add hlin (hexp.const_mul _), integral_add (integrable_const _) (hXi.const_mul _),
        integral_const_mul, hmean, integral_const_mul]
      simp only [mul_zero, add_zero, integral_const, probReal_univ, one_smul]
      rfl
    rw [hm] at hh
    apply hh.trans
    have hc : t^2*A*M ≤ squareExpMgfConstant τ M*t^2 := by
      dsimp [squareExpMgfConstant, A]
      have hn : 0 ≤ (M+1/(4*τ))*t^2 := by positivity
      nlinarith only [hn]
    calc
      _ = t^2*A*M+1 := by ring
      _ ≤ Real.exp (t^2*A*M) := Real.add_one_le_exp _
      _ ≤ _ := Real.exp_le_exp.mpr hc
  · have ht2 : 1 ≤ t^2 := by nlinarith [sq_abs t]
    have hMe : M ≤ Real.exp M := le_trans (by linarith) (Real.add_one_le_exp M)
    apply hlarge.trans
    calc
      _ ≤ Real.exp (t^2/(4*τ))*Real.exp M :=
        mul_le_mul_of_nonneg_left hMe (Real.exp_nonneg _)
      _ = Real.exp (t^2/(4*τ)+M) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hm2 := mul_le_mul_of_nonneg_left ht2 hM
        have han : 0 ≤ A*M*t^2 := by positivity
        calc
          _ ≤ t^2/(4*τ)+M*t^2 := add_le_add le_rfl (by simpa using hm2)
          _ ≤ t^2/(4*τ)+M*t^2+A*M*t^2 := le_add_of_nonneg_right han
          _ = squareExpMgfConstant τ M*t^2 := by dsimp [squareExpMgfConstant, A]; ring

#print axioms squareExp_projected_mgf
end SpectralRadiusUpperTail
