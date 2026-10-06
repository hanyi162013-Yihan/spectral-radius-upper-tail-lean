import SpectralRadiusUpperTail.IidSignedMultiplicityExcess
import SpectralRadiusUpperTail.MultiplicityProductBound
import SpectralRadiusUpperTail.FactorialMomentEnvelope

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {σ τ 𝕂 : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
  [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

noncomputable def signedWordMomentBase (μ : Measure 𝕂) (c : ℝ) (N : ℕ) : ℝ :=
  max 1 (2*∫ z : 𝕂, Real.exp (c*‖z‖^2) ∂μ) * (((N : ℝ)+1)*(1+1/c))

lemma signedWordMomentBase_one_le (μ : Measure 𝕂) (c : ℝ) (hc : 0 < c) (N : ℕ) :
    1 ≤ signedWordMomentBase μ c N := by
  unfold signedWordMomentBase
  have hA : 1 ≤ max 1 (2*∫ z : 𝕂, Real.exp (c*‖z‖^2) ∂μ) := le_max_left _ _
  have hB : 1 ≤ ((N : ℝ)+1)*(1+1/c) := by
    have hu : 0 ≤ 1/c := by positivity
    nlinarith [(show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)]
  nlinarith

/-- Actual iid word moment cost is controlled by multiplicity excess, not total length. -/
lemma iidSignedWord_excess_moment_bound (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1)
    (e : τ → σ) (s : τ → Bool) :
    ‖∫ x : σ → 𝕂, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)‖ ≤
    (signedWordMomentBase μ c (Fintype.card τ))^(3*∑ i, (entryMultiplicity e i-2)) := by
  by_cases hz : (∫ x : σ → 𝕂, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)) = 0
  · rw [hz,norm_zero]
    exact pow_nonneg (le_trans (by norm_num) (signedWordMomentBase_one_le μ c hc _)) _
  have hsingle := iidSignedWord_no_singleton μ hm e s hz
  rw [iidSignedWord_expectation, norm_prod]
  apply multiplicity_product_excess_bound (entryMultiplicity e) _ _
    (signedWordMomentBase_one_le μ c hc _) (fun _ => norm_nonneg _)
  · intro i hi
    have hcounts := signedMultiplicity_add e s i
    have hn := hsingle i
    have hd : entryMultiplicity e i = 0 ∨ entryMultiplicity e i = 2 := by omega
    rcases hd with hd | hd
    · have ha : entryMultiplicity (fun t => (e t,s t)) (i,false) = 0 := by omega
      have hb : entryMultiplicity (fun t => (e t,s t)) (i,true) = 0 := by omega
      simp [ha,hb]
    · exact mixedMoment_degree_two_norm_le μ hv _ _ (hcounts.trans hd)
  · intro i hi
    have hcounts := signedMultiplicity_add e s i
    have hbound : entryMultiplicity e i ≤ Fintype.card τ := by
      unfold entryMultiplicity
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)
    have hM : 0 ≤ ∫ z : 𝕂, Real.exp (c*‖z‖^2) ∂μ :=
      integral_nonneg (fun _ => (Real.exp_pos _).le)
    have hb := factorial_moment_envelope_le _ (1/c) hM (by positivity)
      (entryMultiplicity e i) (Fintype.card τ) (by omega) hbound
    have hmom := squareExp_mixedMoment_norm_le μ c hc hexp
      (entryMultiplicity (fun t => (e t,s t)) (i,false))
      (entryMultiplicity (fun t => (e t,s t)) (i,true))
    rw [hcounts] at hmom
    exact hmom.trans hb

#print axioms signedWordMomentBase
#print axioms signedWordMomentBase_one_le
#print axioms iidSignedWord_excess_moment_bound
end SpectralRadiusUpperTail
