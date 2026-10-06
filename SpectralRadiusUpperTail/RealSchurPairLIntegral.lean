import SpectralRadiusUpperTail.RealSchurPairInverseDensity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- Nonnegative version of the positive pair chart formula. It applies
without prior integrability when the outer Schur observable is unbounded. -/
theorem realSchurPair_chart_lintegral (g : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ q in realSchurPairCoordinateDomain, g q) =
      ∫⁻ p in realSchurPositivePairDomain,
        ENNReal.ofReal (2*(p.1-p.2)*(p.1+p.2))*g (realSchurPairCoordinates p.1 p.2) := by
  have hinj : Set.InjOn (fun p : ℝ × ℝ => realSchurPairCoordinates p.1 p.2)
      realSchurPositivePairDomain := by
    intro p hp q hq hpq
    change 0 < p.2 ∧ p.2 < p.1 at hp
    change 0 < q.2 ∧ q.2 < q.1 at hq
    change realSchurPairCoordinates p.1 p.2=realSchurPairCoordinates q.1 q.2 at hpq
    calc
      p = realSchurPairFromCoordinates (realSchurPairCoordinates p.1 p.2).1
          (realSchurPairCoordinates p.1 p.2).2 := (realSchur_pair_chart_backward p.1 p.2 hp.1 hp.2).symm
      _ = realSchurPairFromCoordinates (realSchurPairCoordinates q.1 q.2).1
          (realSchurPairCoordinates q.1 q.2).2 := by rw [hpq]
      _ = q := realSchur_pair_chart_backward q.1 q.2 hq.1 hq.2
  have himage : (fun p : ℝ × ℝ => realSchurPairCoordinates p.1 p.2) ''
      realSchurPositivePairDomain=realSchurPairCoordinateDomain := by
    ext q
    constructor
    · rintro ⟨p,hp,rfl⟩
      change 0 < p.2 ∧ p.2 < p.1 at hp
      exact ⟨mul_pos (lt_trans hp.1 hp.2) hp.1,sq_pos_of_pos (sub_pos.mpr hp.2)⟩
    · intro hq
      change 0 < q.1 ∧ 0 < q.2 at hq
      exact ⟨realSchurPairFromCoordinates q.1 q.2,
        realSchur_pair_chart_pos q.1 q.2 hq.1 hq.2,
        realSchur_pair_chart_forward q.1 q.2 hq.1 hq.2⟩
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (f := fun p : ℝ × ℝ => realSchurPairCoordinates p.1 p.2)
    (f' := fun p => realSchurPairChartLinear p.1 p.2) volume
    realSchurPositivePairDomain_isOpen.measurableSet
    (fun p _ => (realSchurPairCoordinates_hasFDerivAt p.1 p.2).hasFDerivWithinAt) hinj g
  rw [himage] at h
  refine h.trans ?_
  apply setLIntegral_congr_fun realSchurPositivePairDomain_isOpen.measurableSet
  intro p hp
  dsimp only
  rw [realSchurPair_chart_abs_det p.1 p.2 hp.1 hp.2]

/-- The reciprocal-Jacobian formula for arbitrary nonnegative tests. -/
theorem realSchurPair_inverse_density_lintegral (g : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in realSchurPositivePairDomain, g p) =
      ∫⁻ q in realSchurPairCoordinateDomain,
        ENNReal.ofReal (realSchurPairInverseJacobian q.1 q.2) *
          g (realSchurPairFromCoordinates q.1 q.2) := by
  rw [realSchurPair_chart_lintegral]
  apply setLIntegral_congr_fun realSchurPositivePairDomain_isOpen.measurableSet
  intro p hp
  dsimp only
  have hp' : 0 < p.2 ∧ p.2 < p.1 := hp
  have hdiff : 0 < p.1-p.2 := sub_pos.mpr hp'.2
  have hfirst : 0 < p.1 := lt_trans hp'.1 hp'.2
  rw [realSchur_pair_chart_backward p.1 p.2 hp'.1 hp'.2,← mul_assoc,
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hdiff.le)
      (add_nonneg hfirst.le hp'.1.le)),
    realSchurPairInverseJacobian_cancel p.1 p.2 hp'.1 hp'.2,ENNReal.ofReal_one,one_mul]

#print axioms realSchurPair_chart_lintegral
#print axioms realSchurPair_inverse_density_lintegral
end SpectralRadiusUpperTail
