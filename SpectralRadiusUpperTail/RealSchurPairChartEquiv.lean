import SpectralRadiusUpperTail.RealSchurPairChart
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The usual positive off-diagonal chart for a real Schur conjugate-pair
block, with distinct singular values. -/
def realSchurPositivePairDomain : Set (ℝ × ℝ) :=
  {p | 0 < p.2 ∧ p.2 < p.1}

/-- Squared spectral-imaginary and gap coordinates on that chart. -/
def realSchurPairCoordinateDomain : Set (ℝ × ℝ) :=
  {q | 0 < q.1 ∧ 0 < q.2}

theorem realSchurPositivePairDomain_isOpen :
    IsOpen realSchurPositivePairDomain := by
  unfold realSchurPositivePairDomain
  exact (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd continuous_fst)

theorem realSchurPairCoordinateDomain_isOpen :
    IsOpen realSchurPairCoordinateDomain := by
  unfold realSchurPairCoordinateDomain
  exact (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_const continuous_snd)

/-- The explicit global inverse on the chosen open two-dimensional chart. -/
noncomputable def realSchurPairChartEquiv :
    realSchurPositivePairDomain ≃ realSchurPairCoordinateDomain where
  toFun p := by
    refine ⟨realSchurPairCoordinates p.1.1 p.1.2, ?_⟩
    rcases p.2 with ⟨hc, hcb⟩
    change 0 < p.1.1*p.1.2 ∧ 0 < (p.1.1-p.1.2)^2
    exact ⟨mul_pos (lt_trans hc hcb) hc,
      sq_pos_of_pos (sub_pos.mpr hcb)⟩
  invFun q := by
    refine ⟨realSchurPairFromCoordinates q.1.1 q.1.2, ?_⟩
    exact realSchur_pair_chart_pos q.1.1 q.1.2 q.2.1 q.2.2
  left_inv p := by
    apply Subtype.ext
    exact realSchur_pair_chart_backward p.1.1 p.1.2 p.2.1 p.2.2
  right_inv q := by
    apply Subtype.ext
    exact realSchur_pair_chart_forward q.1.1 q.1.2 q.2.1 q.2.2

theorem realSchurPairCoordinates_continuous :
    Continuous (fun p : ℝ × ℝ => realSchurPairCoordinates p.1 p.2) := by
  unfold realSchurPairCoordinates
  fun_prop

theorem realSchurPairFromCoordinates_continuous :
    Continuous (fun q : ℝ × ℝ => realSchurPairFromCoordinates q.1 q.2) := by
  unfold realSchurPairFromCoordinates
  fun_prop

/-- The pair coordinates form a homeomorphism of the two open charts. -/
noncomputable def realSchurPairChartHomeomorph :
    realSchurPositivePairDomain ≃ₜ realSchurPairCoordinateDomain where
  toEquiv := realSchurPairChartEquiv
  continuous_toFun := by
    change Continuous (fun p : realSchurPositivePairDomain =>
      (⟨realSchurPairCoordinates p.1.1 p.1.2,
        (realSchurPairChartEquiv p).2⟩ : realSchurPairCoordinateDomain))
    exact (realSchurPairCoordinates_continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    change Continuous (fun q : realSchurPairCoordinateDomain =>
      (⟨realSchurPairFromCoordinates q.1.1 q.1.2,
        (realSchurPairChartEquiv.symm q).2⟩ : realSchurPositivePairDomain))
    exact (realSchurPairFromCoordinates_continuous.comp continuous_subtype_val).subtype_mk _

#print axioms realSchurPairChartEquiv
#print axioms realSchurPairChartHomeomorph
end SpectralRadiusUpperTail
