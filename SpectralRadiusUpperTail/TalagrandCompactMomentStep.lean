import SpectralRadiusUpperTail.TalagrandConcreteFiberBound
import SpectralRadiusUpperTail.TalagrandAveragedFiberStep
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂]

/-- The positive-probability compact-set induction step after the two
product-measure Fubini identities. The concrete fiber estimate and scalar
average are both applied here; only the named Fubini/measurability data and
the lower-dimensional moment hypotheses are supplied. -/
theorem talagrand_compact_moment_step
    (N : ℕ)
    [MeasurableSpace (EuclideanSpace 𝕂 (Fin N))]
    [BorelSpace (EuclideanSpace 𝕂 (Fin N))]
    [MeasurableSpace (EuclideanSpace 𝕂 (Fin (N+1)))]
    [BorelSpace (EuclideanSpace 𝕂 (Fin (N+1)))]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (ν : Measure (EuclideanSpace 𝕂 (Fin N))) [IsProbabilityMeasure ν]
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1))))
    (hA : IsCompact A) (hAne : A.Nonempty)
    (pA I : ℝ) (hpA : 0 < pA)
    (pB : ℝ) (hpB : 0 < pB)
    (hpBdef : pB = ν.real (euclideanCoordinateTail N '' A))
    (hPFmeas : Measurable (fun s : 𝕂 =>
      ν.real {y : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s y ∈ A}))
    (hMass : pA = ∫ s, ν.real
      {y : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s y ∈ A} ∂μ)
    (hJint : Integrable (fun s : 𝕂 =>
      ∫ y, Real.exp
        (mismatchHullEnergy (euclideanWithHead N s y) A/4) ∂ν) μ)
    (hIntegral : I = ∫ s, ∫ y, Real.exp
      (mismatchHullEnergy (euclideanWithHead N s y) A/4) ∂ν ∂μ)
    (hBmoment : (∫ y,
      Real.exp (mismatchHullEnergy y (euclideanCoordinateTail N '' A)/4) ∂ν) ≤ 1/pB)
    (hFmoment : ∀ s : 𝕂, ∀ pF : ℝ, 0 < pF →
      pF = ν.real {y : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s y ∈ A} →
      (∫ y, Real.exp (mismatchHullEnergy y
        {z : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s z ∈ A}/4) ∂ν) ≤ 1/pF) :
    pA*I ≤ 1 := by
  let B := euclideanCoordinateTail N '' A
  let pF := fun s : 𝕂 => ν.real
    {y : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s y ∈ A}
  let a := fun s : 𝕂 => pF s/pB
  let J := fun s : 𝕂 => ∫ y, Real.exp
    (mismatchHullEnergy (euclideanWithHead N s y) A/4) ∂ν
  have hFsubB (s : 𝕂) :
      {y : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s y ∈ A} ⊆ B := by
    intro y hy
    refine ⟨euclideanWithHead N s y, hy, ?_⟩
    ext i
    rfl
  have haMeas : Measurable a := hPFmeas.div_const pB
  have haRange : ∀ᵐ s ∂μ, 0 ≤ a s ∧ a s ≤ 1 := by
    filter_upwards [] with s
    have hP0 : 0 ≤ pF s := measureReal_nonneg
    have hPle : pF s ≤ pB := by
      rw [hpBdef]
      exact measureReal_mono (hFsubB s)
    exact ⟨div_nonneg hP0 hpB.le, (div_le_one hpB).mpr hPle⟩
  have hMean : (∫ s, a s ∂μ) = pA/pB := by
    dsimp [a]
    rw [integral_div, ← hMass]
  have hMeanPos : 0 < ∫ s, a s ∂μ := by
    rw [hMean]
    exact div_pos hpA hpB
  have hJpoint : ∀ᵐ s ∂μ, J s ≤
      (1/pB)*Real.exp
        (-talagrandWeight (a s)*Real.log (a s)+
          (1-talagrandWeight (a s))^2/4) := by
    filter_upwards [] with s
    exact talagrand_concrete_fiber_bound N ν A hA hAne s
      pB hpB hpBdef hBmoment (hFmoment s)
  have hstep := talagrand_averaged_fiber_step μ pB hpB
    a J haMeas haRange hMeanPos hJint hJpoint
  calc
    pA*I = pB*(∫ s, a s ∂μ)*(∫ s, J s ∂μ) := by
      rw [hMean, hIntegral]
      field_simp
      rfl
    _ ≤ 1 := hstep

#print axioms talagrand_compact_moment_step
end SpectralRadiusUpperTail
