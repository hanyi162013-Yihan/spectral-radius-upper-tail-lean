import SpectralRadiusUpperTail.GaussianComparatorPower

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Fixed positive powers vanish against deterministic unit-energy vectors
on the actual retained coupling, even when the tilt parameters vary with n. -/
lemma gaussianComparatorPower_probability_tendsto (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (k : ℕ) (hk : 0 < k)
    (p q : (n : ℕ) → Fin n → 𝕂)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1) (hq : ∀ n, (∑ i, ‖q n i‖^2) ≤ 1)
    (v : ℕ → ℕ → 𝕂) (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (t : (n : ℕ) → Fin n → 𝕂) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (gaussianSequentialMatrixLaw μ (v n) (a n) (t n)).real
      {x | ε ≤ ‖∑ i, star (p n i) *
        ((normalizedArray (fun j => comparatorVector n (x j)))^k).mulVec (q n) i‖})
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg))
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact gaussianComparatorPower_probability_le μ c hc hexp hm hk hn
      (p n) (q n) (hp n) (hq n) (v n) (a n) (ha n) (t n) ε hε
  · have h : Tendsto (fun n : ℕ => pairedMomentConstant μ k/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [zero_div] using h.div_const (ε^2)

#print axioms gaussianComparatorPower_probability_tendsto
end SpectralRadiusUpperTail
