import SpectralRadiusUpperTail.RealSchurPairGapWeightJacobian
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Pointwise density of one positive real Schur conjugate-pair chart in
`(u=bc,s=(b-c)^2)` coordinates, including its angular orbit factor. -/
theorem realSchur_pair_gaussian_chart_pointwise
    (n x u s : ℝ) (hu : 0 < u) (hs : 0 < s) :
    let p := realSchurPairFromCoordinates u s
    |Matrix.det (realSchurPairOrbitJacobian p.1 p.2)| *
      Real.exp (-(n/2)*(2*x^2+p.1^2+p.2^2)) *
      realSchurPairInverseJacobian u s =
        (Real.sqrt (s+4*u))⁻¹ *
          (Real.exp (-n*(x^2+u)) * Real.exp (-(n/2)*s)) := by
  dsimp
  let p := realSchurPairFromCoordinates u s
  have hp := realSchur_pair_chart_pos u s hu hs
  have hcoord := realSchur_pair_chart_forward u s hu hs
  have hfirst : p.1*p.2 = u := by
    have hh := congrArg Prod.fst hcoord
    change p.1*p.2 = u at hh
    exact hh
  have hsecond : (p.1-p.2)^2 = s := by
    have hh := congrArg Prod.snd hcoord
    change (p.1-p.2)^2 = s at hh
    exact hh
  have hy : (Real.sqrt u)^2 = u := Real.sq_sqrt hu.le
  have hbc : p.1*p.2 = (Real.sqrt u)^2 := by rw [hy]; exact hfirst
  have hweight := realSchur_pair_local_gaussian_factor
    n x p.1 p.2 (Real.sqrt u) hp.1 hp.2 hbc
  have hgap : schurGapWeight (Real.sqrt u) s =
      (Real.sqrt (s+4*u))⁻¹ := by
    unfold schurGapWeight
    rw [max_eq_right hs.le, hy]
  calc
    |Matrix.det (realSchurPairOrbitJacobian p.1 p.2)| *
        Real.exp (-(n/2)*(2*x^2+p.1^2+p.2^2)) *
        realSchurPairInverseJacobian u s =
      |Matrix.det (realSchurPairOrbitJacobian p.1 p.2)| *
        realSchurPairInverseJacobian
          (realSchurPairCoordinates p.1 p.2).1
          (realSchurPairCoordinates p.1 p.2).2 *
        Real.exp (-(n/2)*(2*x^2+p.1^2+p.2^2)) := by
          rw [hcoord]
          ring
    _ = schurGapWeight (Real.sqrt u) ((p.1-p.2)^2) *
          (Real.exp (-n*(x^2+(Real.sqrt u)^2)) *
            Real.exp (-(n/2)*(p.1-p.2)^2)) := hweight
    _ = _ := by rw [hsecond, hy, hgap]

/-- Exact local Gaussian change of variables for every real test function.
It still concerns one 2×2 chart; no global Schur decomposition or finite-n
real Ginibre one-point formula is claimed. -/
theorem realSchur_pair_gaussian_chart_integral
    (n x : ℝ) (F : ℝ × ℝ → ℝ) :
    (∫ p in realSchurPositivePairDomain,
      |Matrix.det (realSchurPairOrbitJacobian p.1 p.2)| *
        Real.exp (-(n/2)*(2*x^2+p.1^2+p.2^2)) *
        F (realSchurPairCoordinates p.1 p.2)) =
      ∫ q in realSchurPairCoordinateDomain,
        (Real.sqrt (q.2+4*q.1))⁻¹ *
          (Real.exp (-n*(x^2+q.1)) *
            Real.exp (-(n/2)*q.2)) * F q := by
  let G : ℝ × ℝ → ℝ := fun p =>
    |Matrix.det (realSchurPairOrbitJacobian p.1 p.2)| *
      Real.exp (-(n/2)*(2*x^2+p.1^2+p.2^2)) *
      F (realSchurPairCoordinates p.1 p.2)
  have hcov := realSchurPair_inverse_density_integral G
  calc
    (∫ p in realSchurPositivePairDomain, G p) =
      ∫ q in realSchurPairCoordinateDomain,
        G (realSchurPairFromCoordinates q.1 q.2) *
          realSchurPairInverseJacobian q.1 q.2 := hcov
    _ = ∫ q in realSchurPairCoordinateDomain,
        (Real.sqrt (q.2+4*q.1))⁻¹ *
          (Real.exp (-n*(x^2+q.1)) *
            Real.exp (-(n/2)*q.2)) * F q := by
      apply setIntegral_congr_fun realSchurPairCoordinateDomain_isOpen.measurableSet
      intro q hq
      change 0 < q.1 ∧ 0 < q.2 at hq
      have hcoord := realSchur_pair_chart_forward q.1 q.2 hq.1 hq.2
      have hpoint := realSchur_pair_gaussian_chart_pointwise
        n x q.1 q.2 hq.1 hq.2
      dsimp [G]
      rw [hcoord]
      calc
        _ = (|Matrix.det
              (realSchurPairOrbitJacobian
                (realSchurPairFromCoordinates q.1 q.2).1
                (realSchurPairFromCoordinates q.1 q.2).2)| *
              Real.exp (-(n/2)*(2*x^2+
                (realSchurPairFromCoordinates q.1 q.2).1^2+
                (realSchurPairFromCoordinates q.1 q.2).2^2)) *
              realSchurPairInverseJacobian q.1 q.2) * F q := by ring
        _ = _ := by rw [hpoint]
    
#print axioms realSchur_pair_gaussian_chart_pointwise
#print axioms realSchur_pair_gaussian_chart_integral
end SpectralRadiusUpperTail
