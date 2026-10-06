import SpectralRadiusUpperTail.RealSchurMixedSimpleSpectrum
import Mathlib.Algebra.MvPolynomial.Monad

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- A polynomial matrix family has simple spectrum almost everywhere
once one parameter value has simple spectrum. -/
theorem polynomialMatrix_charpoly_separable_ae
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (p : ι × ι → MvPolynomial κ ℝ)
    (a : κ → ℝ)
    (ha : (Matrix.of (fun ij => MvPolynomial.eval a (p ij)).curry).charpoly.Separable) :
    ∀ᵐ x : κ → ℝ,
      (Matrix.of (fun ij => MvPolynomial.eval x (p ij)).curry).charpoly.Separable := by
  let q := MvPolynomial.bind₁ p (finiteRealMatrixCollisionPolynomial ι)
  have he (x : κ → ℝ) : MvPolynomial.eval x q =
      MvPolynomial.eval (fun ij => MvPolynomial.eval x (p ij))
        (finiteRealMatrixCollisionPolynomial ι) := by
    change MvPolynomial.eval₂Hom (RingHom.id ℝ) x
      (MvPolynomial.bind₁ p (finiteRealMatrixCollisionPolynomial ι))=_
    exact MvPolynomial.eval₂Hom_bind₁ _ _ _ _
  have hq : q ≠ 0 := by
    intro hzero
    have h := (finiteRealMatrixCollisionPolynomial_eval_ne_zero_iff ι
      (fun ij => MvPolynomial.eval a (p ij))).mpr ha
    rw [← he a,hzero,map_zero] at h
    exact h rfl
  have h := mvPolynomial_eval_ne_zero_ae_pi
    (fun _ : κ => (volume : Measure ℝ)) q hq
  filter_upwards [h] with x hx
  apply (finiteRealMatrixCollisionPolynomial_eval_ne_zero_iff ι _).mp
  rwa [← he x]

#print axioms polynomialMatrix_charpoly_separable_ae
end SpectralRadiusUpperTail
