import SpectralRadiusUpperTail.ComplexFiniteUpperBound
import SpectralRadiusUpperTail.ExponentialPrefactorBudget

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Conditional assembly: the annealed, bulk and norm-tail inputs are explicit. -/
lemma complex_upper_from_three_inputs
    (P : (n : ℕ) → Measure (Fin n → Fin n → ℂ)) [∀ n, IsProbabilityMeasure (P n)]
    (r : ℝ) (hr : 1 < r)
    (hnorm : ∀ K : ℝ, 0 < K → ∃ R : ℝ, r < R ∧ ∀ᶠ n : ℕ in atTop,
      (P n).real {x | R < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖} ≤ Real.exp (-K*(n : ℝ)))
    (hbulk : ∃ M : ℝ, 0 < M ∧ ∀ R u ε : ℝ, 0 < u → 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
          (P n).real {x | 2*Real.log ‖z‖+2*u*M^2+ε <
            regularizedResidualLogDet x z (2*u)/(n : ℝ)} ≤ C*Real.exp (-q*(n : ℝ)^2))
    (hannealed : ∀ R u ε : ℝ, 0 < u → 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
        (∫⁻ x, fullSpectralSphereWeight n u z x ∂P n) ≤
          ENNReal.ofReal (Real.exp ((n : ℝ)*(complexAnnealedExponent u ‖z‖+ε))))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (P n).real {x | r ≤ (spectralRadius ℂ (normalizedArray x)).toReal} ≤
        Real.exp ((n : ℝ)*(-rate 2 r+ε)) := by
  obtain ⟨M, hM, hb⟩ := hbulk
  let K := rate 2 r+1
  have hK : 0 < K := by have hh := rate_pos 2 r (by norm_num) hr; dsimp [K]; linarith
  obtain ⟨R, hrR, hN⟩ := hnorm K hK
  let D := 1+R^2+2*M^2
  have hD : 0 < D := by dsimp [D]; positivity
  let u := ε/(4*D)
  have hu : 0 < u := by dsimp [u]; positivity
  have heu : u*D = ε/4 := by dsimp [u]; field_simp
  obtain ⟨S, hS, hcover⟩ := complex_annulus_finite_cover r R u hu
  obtain ⟨C, hC, q, hq, hB⟩ := hb R u (ε/8) hu (by positivity)
  have hA := hannealed R u (ε/8) hu (by positivity)
  let a := -rate 2 r+u*D+2*(ε/8)
  have hba : -K ≤ a := by dsimp [K, a]; nlinarith [mul_pos hu hD]
  have hbudget := eventually_three_exponential_terms (S.card : ℝ) ((S.card : ℝ)*C) q a (-K) (ε/2)
    (Nat.cast_nonneg _) (by positivity) hq hba (by positivity)
  filter_upwards [hN, hB, hA, hbudget, eventually_gt_atTop 0] with n hnN hnB hnA hnBudget hn
  have hnorm' : (P n).real {x | R < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖} ≤
      Real.exp ((n : ℝ)*(-K)) := by convert! hnN using 1 <;> ring
  have hfinite := complex_finite_upper_bound n hn u r R M (ε/8) C q (Real.exp ((n : ℝ)*(-K)))
    hu hr S hS hcover (P n)
    (fun z hz => hnA z (hS z hz).1 (hS z hz).2)
    (fun z hz => hnB z (hS z hz).1 (hS z hz).2) hnorm'
  have hh := hfinite.trans hnBudget
  convert! hh using 1
  congr 2
  dsimp [a]
  rw [heu]
  ring

#print axioms complex_upper_from_three_inputs
end SpectralRadiusUpperTail
