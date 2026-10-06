import SpectralRadiusUpperTail.ComplexAnnulusProbability

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

lemma complex_finite_upper_bound (n : ℕ) (hn : 0 < n)
    (u r R M ε C q T : ℝ) (hu : 0 < u) (hr : 1 < r) (S : Finset ℂ)
    (hS : ∀ z ∈ S, r ≤ ‖z‖ ∧ ‖z‖ ≤ R)
    (hcover : ∀ w : ℂ, r ≤ ‖w‖ → ‖w‖ ≤ R → ∃ z ∈ S, ‖w-z‖ < u)
    (P : Measure (Fin n → Fin n → ℂ)) [IsFiniteMeasure P]
    (hA : ∀ z ∈ S, (∫⁻ x, fullSpectralSphereWeight n u z x ∂P) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ)*(complexAnnealedExponent u ‖z‖+ε))))
    (hbulk : ∀ z ∈ S, P.real {x | 2*Real.log ‖z‖+2*u*M^2+ε <
      regularizedResidualLogDet x z (2*u)/(n : ℝ)} ≤ C*Real.exp (-q*(n : ℝ)^2))
    (hnorm : P.real {x | R < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖} ≤ T) :
    P.real {x | r ≤ (spectralRadius ℂ (normalizedArray x)).toReal} ≤
      (S.card : ℝ)*Real.exp ((n : ℝ)*(-rate 2 r+u*(1+R^2+2*M^2)+2*ε))+
      ((S.card : ℝ)*C)*Real.exp (-q*(n : ℝ)^2)+T := by
  let B := fun z => {x : Fin n → Fin n → ℂ | 2*Real.log ‖z‖+2*u*M^2+ε <
    regularizedResidualLogDet x z (2*u)/(n : ℝ)}
  let N := {x : Fin n → Fin n → ℂ | R < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖}
  let G := {x : Fin n → Fin n → ℂ | r ≤ (spectralRadius ℂ (normalizedArray x)).toReal ∧
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖ ≤ R ∧
    ∀ z ∈ S, regularizedResidualLogDet x z (2*u)/(n : ℝ) ≤ 2*Real.log ‖z‖+2*u*M^2+ε}
  have hg := ENNReal.toReal_mono (by finiteness)
    (complex_annulus_probability_of_annealed n hn u r R M ε hu hr S hS hcover P hA)
  have hg' : P.real G ≤ (S.card : ℝ)*Real.exp ((n : ℝ)*(-rate 2 r+u*(1+R^2+2*M^2)+2*ε)) := by
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using hg
  have hb : P.real (⋃ z ∈ S, B z) ≤ ((S.card : ℝ)*C)*Real.exp (-q*(n : ℝ)^2) := by
    apply (measureReal_biUnion_finset_le S B).trans
    have hh := Finset.sum_le_sum (fun z hz => hbulk z hz)
    simpa only [B, Finset.sum_const, nsmul_eq_mul, mul_assoc] using hh
  have hset : {x | r ≤ (spectralRadius ℂ (normalizedArray x)).toReal} ⊆
      (G ∪ (⋃ z ∈ S, B z)) ∪ N := by
    intro x hx
    by_contra h
    have hxn : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖ ≤ R := by
      by_contra hnot
      exact h (Or.inr (lt_of_not_ge hnot))
    have hxb : ∀ z ∈ S, regularizedResidualLogDet x z (2*u)/(n : ℝ) ≤
        2*Real.log ‖z‖+2*u*M^2+ε := by
      intro z hz
      by_contra hnot
      exact h (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, lt_of_not_ge hnot⟩⟩)))
    exact h (Or.inl (Or.inl ⟨hx, hxn, hxb⟩))
  apply (measureReal_mono (μ := P) hset).trans
  apply (measureReal_union_le _ _).trans
  apply add_le_add _ hnorm
  exact (measureReal_union_le _ _).trans (add_le_add hg' hb)

#print axioms complex_finite_upper_bound
end SpectralRadiusUpperTail
