import SpectralRadiusUpperTail.RealRootRankUniqueness
import SpectralRadiusUpperTail.RealMatrixMeasurableSpectrumRoots
import SpectralRadiusUpperTail.PolynomialComplexRealRootFilter
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial MeasureTheory

/-- On simple real polynomials, real-root rank equals the number of
complex roots lying on the real axis to the left of the marked scalar. -/
theorem realPolynomialRootRank_eq_complexCount
    (p : ℝ[X]) (hp : p ≠ 0) (hsep : p.Separable) (t : ℝ) :
    realPolynomialRootRank p t =
      Multiset.countP (fun z : ℂ => z.im = 0 ∧ z.re < t)
        (p.aroots ℂ) := by
  classical
  calc
    realPolynomialRootRank p t =
        Multiset.countP (fun x : ℝ => x < t) p.roots := by
      exact (polynomial_simpleRealRoot_countP_eq_ncard
        p hp hsep (fun x : ℝ => x < t)).symm
    _ = Multiset.countP (fun z : ℂ => z.re < t)
          (p.roots.map (fun x : ℝ => (x : ℂ))) := by
      rw [Multiset.countP_map]
      simp [Multiset.countP_eq_card_filter]
    _ = Multiset.countP (fun z : ℂ => z.re < t)
          ((p.aroots ℂ).filter (fun z => z.im = 0)) := by
      rw [realPolynomial_aroots_filter_real]
    _ = _ := by
      simp [Multiset.countP_eq_card_filter, Multiset.filter_filter, and_comm]

/-- The measurable Schur labels compute the root rank of each simple
real matrix. -/
theorem realMatrixRootRank_eq_measurableSpectrumCount
    (n : ℕ) (x : (Fin n × Fin n) → ℝ) (t : ℝ)
    (hx : (Matrix.of x.curry).charpoly.Separable) :
    realPolynomialRootRank (Matrix.of x.curry).charpoly t =
      ∑ i : Fin n,
        if (realGaussianMeasurableRawSpectrum n x i).im = 0 ∧
            (realGaussianMeasurableRawSpectrum n x i).re < t
        then 1 else 0 := by
  classical
  let A := Matrix.of x.curry
  have hp : A.charpoly ≠ 0 := A.charpoly_monic.ne_zero
  rw [realPolynomialRootRank_eq_complexCount A.charpoly hp hx t]
  have hroots := realMatrixMeasurableRawSpectrum_roots_of_separable n x hx
  rw [show A.charpoly.aroots ℂ =
      ((A.map Complex.ofRealHom).charpoly).roots by
        rw [Matrix.charpoly_map]
        rfl,
    hroots, Multiset.countP_map]
  change (Finset.univ.filter
    (fun i : Fin n => (realGaussianMeasurableRawSpectrum n x i).im = 0 ∧
      (realGaussianMeasurableRawSpectrum n x i).re < t)).card = _
  simp [Finset.sum_boole]

#print axioms realPolynomialRootRank_eq_complexCount
#print axioms realMatrixRootRank_eq_measurableSpectrumCount
end SpectralRadiusUpperTail
