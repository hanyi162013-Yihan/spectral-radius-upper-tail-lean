import SpectralRadiusUpperTail.RealSchurPairChartDerivative
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

private theorem realSchurPairCoordinates_injOn :
    InjOn (fun p : ℝ × ℝ => realSchurPairCoordinates p.1 p.2)
      realSchurPositivePairDomain := by
  intro p hp q hq hpq
  change 0 < p.2 ∧ p.2 < p.1 at hp
  change 0 < q.2 ∧ q.2 < q.1 at hq
  change realSchurPairCoordinates p.1 p.2 =
    realSchurPairCoordinates q.1 q.2 at hpq
  have hpb := realSchur_pair_chart_backward p.1 p.2 hp.1 hp.2
  have hqb := realSchur_pair_chart_backward q.1 q.2 hq.1 hq.2
  calc
    p = realSchurPairFromCoordinates
      (realSchurPairCoordinates p.1 p.2).1
      (realSchurPairCoordinates p.1 p.2).2 := hpb.symm
    _ = realSchurPairFromCoordinates
      (realSchurPairCoordinates q.1 q.2).1
      (realSchurPairCoordinates q.1 q.2).2 := by rw [hpq]
    _ = q := hqb

private theorem realSchurPairCoordinates_image :
    (fun p : ℝ × ℝ => realSchurPairCoordinates p.1 p.2) ''
      realSchurPositivePairDomain = realSchurPairCoordinateDomain := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change 0 < p.2 ∧ p.2 < p.1 at hp
    change 0 < p.1*p.2 ∧ 0 < (p.1-p.2)^2
    exact ⟨mul_pos (lt_trans hp.1 hp.2) hp.1,
      sq_pos_of_pos (sub_pos.mpr hp.2)⟩
  · intro hq
    change 0 < q.1 ∧ 0 < q.2 at hq
    refine ⟨realSchurPairFromCoordinates q.1 q.2, ?_, ?_⟩
    · exact realSchur_pair_chart_pos q.1 q.2 hq.1 hq.2
    · exact realSchur_pair_chart_forward q.1 q.2 hq.1 hq.2

/-- Genuine two-dimensional change of variables on one positive real Schur
pair chart. It does not yet include the orthogonal-conjugation coordinates
or the global mixed-block Jacobian. -/
theorem realSchurPair_chart_integral (g : ℝ × ℝ → ℝ) :
    (∫ q in realSchurPairCoordinateDomain, g q) =
      ∫ p in realSchurPositivePairDomain,
        |(realSchurPairChartLinear p.1 p.2).det| *
          g (realSchurPairCoordinates p.1 p.2) := by
  have hder : ∀ p ∈ realSchurPositivePairDomain,
      HasFDerivWithinAt
        (fun p : ℝ × ℝ => realSchurPairCoordinates p.1 p.2)
        (realSchurPairChartLinear p.1 p.2)
        realSchurPositivePairDomain p := by
    intro p hp
    exact (realSchurPairCoordinates_hasFDerivAt p.1 p.2).hasFDerivWithinAt
  have h := integral_image_eq_integral_abs_det_fderiv_smul
    (μ := (volume : Measure (ℝ × ℝ)))
    (f := fun p : ℝ × ℝ => realSchurPairCoordinates p.1 p.2)
    (f' := fun p : ℝ × ℝ => realSchurPairChartLinear p.1 p.2)
    realSchurPositivePairDomain_isOpen.measurableSet
    hder realSchurPairCoordinates_injOn g
  rw [realSchurPairCoordinates_image] at h
  simpa only [smul_eq_mul] using h

theorem realSchurPair_chart_abs_det (b c : ℝ)
    (hc : 0 < c) (hcb : c < b) :
    |(realSchurPairChartLinear b c).det| =
      2*(b-c)*(b+c) := by
  rw [ContinuousLinearMap.det, realSchurPairChartLinear_det]
  have hdiff : 0 < b-c := sub_pos.mpr hcb
  have hsum : 0 < b+c := by linarith
  rw [abs_of_nonpos (by nlinarith : -2*(b-c)*(b+c) ≤ 0)]
  ring

/-- Explicit polynomial Jacobian in the forward two-dimensional formula. -/
theorem realSchurPair_chart_integral_explicit (g : ℝ × ℝ → ℝ) :
    (∫ q in realSchurPairCoordinateDomain, g q) =
      ∫ p in realSchurPositivePairDomain,
        2*(p.1-p.2)*(p.1+p.2)*
          g (realSchurPairCoordinates p.1 p.2) := by
  rw [realSchurPair_chart_integral]
  apply setIntegral_congr_fun realSchurPositivePairDomain_isOpen.measurableSet
  intro p hp
  change 0 < p.2 ∧ p.2 < p.1 at hp
  change |(realSchurPairChartLinear p.1 p.2).det| *
    g (realSchurPairCoordinates p.1 p.2) =
      2*(p.1-p.2)*(p.1+p.2)*
        g (realSchurPairCoordinates p.1 p.2)
  rw [realSchurPair_chart_abs_det p.1 p.2 hp.1 hp.2]

#print axioms realSchurPair_chart_abs_det
#print axioms realSchurPair_chart_integral_explicit

#print axioms realSchurPair_chart_integral
end SpectralRadiusUpperTail
