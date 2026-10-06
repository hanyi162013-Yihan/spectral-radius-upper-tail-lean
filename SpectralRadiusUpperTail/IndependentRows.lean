import SpectralRadiusUpperTail.FourPointSoftRow
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FunProp

/-! Sharp planar Laplace bounds for actual finite product row laws. -/
namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def rowRe (a b : ι → ℝ) (x : ι → ℝ × ℝ) : ℝ :=
  ∑ j, (a j*(x j).1-b j*(x j).2)
def rowIm (a b : ι → ℝ) (x : ι → ℝ × ℝ) : ℝ :=
  ∑ j, (b j*(x j).1+a j*(x j).2)
def coefficientMass (a b : ι → ℝ) : ℝ := ∑ j, ((a j)^2+(b j)^2)

lemma row_pairing (a b : ι → ℝ) (u v : ℝ) (x : ι → ℝ × ℝ) :
    2*(u*rowRe a b x+v*rowIm a b x) =
      ∑ j, 2*((u*a j+v*b j)*(x j).1+(-u*b j+v*a j)*(x j).2) := by
  simp only [rowRe, rowIm, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma row_exponential (a b : ι → ℝ) (u v : ℝ) (x : ι → ℝ × ℝ) :
    Real.exp (2*(u*rowRe a b x+v*rowIm a b x)) =
      ∏ j, Real.exp (2*((u*a j+v*b j)*(x j).1+(-u*b j+v*a j)*(x j).2)) := by
  rw [row_pairing, Real.exp_sum]

theorem row_laplace_integrable (μ : ι → Measure (ℝ × ℝ)) [∀ j, SigmaFinite (μ j)]
    (a b : ι → ℝ)
    (hint : ∀ j u v, Integrable (fun x : ℝ × ℝ => Real.exp (2*(u*x.1+v*x.2))) (μ j))
    (u v : ℝ) :
    Integrable (fun x => Real.exp (2*(u*rowRe a b x+v*rowIm a b x))) (Measure.pi μ) := by
  simp_rw [row_exponential]
  exact Integrable.fintype_prod (fun j => hint j _ _)

theorem row_laplace_le (μ : ι → Measure (ℝ × ℝ)) [∀ j, SigmaFinite (μ j)]
    (a b : ι → ℝ)
    (hmgf : ∀ j u v, (∫ x : ℝ × ℝ, Real.exp (2*(u*x.1+v*x.2)) ∂μ j)
      ≤ Real.exp (u^2+v^2)) (u v : ℝ) :
    (∫ x, Real.exp (2*(u*rowRe a b x+v*rowIm a b x)) ∂Measure.pi μ)
      ≤ Real.exp (coefficientMass a b*(u^2+v^2)) := by
  simp_rw [row_exponential]
  rw [integral_fintype_prod_eq_prod (fun j (y : ℝ × ℝ) =>
    Real.exp (2*((u*a j+v*b j)*y.1+(-u*b j+v*a j)*y.2)))]
  calc
    (∏ j, ∫ x : ℝ × ℝ,
        Real.exp (2*((u*a j+v*b j)*x.1+(-u*b j+v*a j)*x.2)) ∂μ j)
      ≤ ∏ j, Real.exp ((u*a j+v*b j)^2+(-u*b j+v*a j)^2) := by
        apply Finset.prod_le_prod
        · intro j _
          exact integral_nonneg (fun _ => (Real.exp_pos _).le)
        · intro j _
          exact hmgf j _ _
    _ = Real.exp (coefficientMass a b*(u^2+v^2)) := by
      rw [← Real.exp_sum]
      congr 1
      unfold coefficientMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem fourPoint_row_laplace_le (a b : ι → ℝ) (u v : ℝ) :
    (∫ x, Real.exp (2*(u*rowRe a b x+v*rowIm a b x))
      ∂Measure.pi (fun _ : ι => fourPointMeasure))
    ≤ Real.exp (coefficientMass a b*(u^2+v^2)) :=
  row_laplace_le (fun _ => fourPointMeasure) a b (fun _ => fourPoint_laplace) u v

#print axioms row_laplace_integrable
#print axioms row_laplace_le
#print axioms fourPoint_row_laplace_le
end SpectralRadiusUpperTail
