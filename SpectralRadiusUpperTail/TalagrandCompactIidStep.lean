import SpectralRadiusUpperTail.TalagrandCompactMomentStep
import SpectralRadiusUpperTail.TalagrandEuclideanProductLaw
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- The compact-set Talagrand induction step for an actual iid product law.
Only the two lower-dimensional moment bounds remain as hypotheses. -/
theorem talagrand_compact_iid_step
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (N : ℕ)
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1))))
    (hA : IsCompact A) (hAne : A.Nonempty)
    (hpA : 0 < (talagrandEuclideanProductLaw μ (N+1)).real A)
    (hBmoment : 0 < (talagrandEuclideanProductLaw μ N).real
        (euclideanCoordinateTail N '' A) →
      (∫ y, Real.exp (mismatchHullEnergy y
        (euclideanCoordinateTail N '' A)/4)
        ∂talagrandEuclideanProductLaw μ N) ≤
      1/(talagrandEuclideanProductLaw μ N).real
        (euclideanCoordinateTail N '' A))
    (hFmoment : ∀ s : 𝕂,
      0 < (talagrandEuclideanProductLaw μ N).real
        {y : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s y ∈ A} →
      (∫ y, Real.exp (mismatchHullEnergy y
        {z : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s z ∈ A}/4)
        ∂talagrandEuclideanProductLaw μ N) ≤
      1/(talagrandEuclideanProductLaw μ N).real
        {y : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s y ∈ A}) :
    (talagrandEuclideanProductLaw μ (N+1)).real A *
      (∫ x, Real.exp (mismatchHullEnergy x A/4)
        ∂talagrandEuclideanProductLaw μ (N+1)) ≤ 1 := by
  let ν := talagrandEuclideanProductLaw μ N
  let pA := (talagrandEuclideanProductLaw μ (N+1)).real A
  let pB := ν.real (euclideanCoordinateTail N '' A)
  let f := fun x : EuclideanSpace 𝕂 (Fin (N+1)) =>
    Real.exp (mismatchHullEnergy x A/4)
  let F := fun s : 𝕂 =>
    {y : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s y ∈ A}
  have hAm : MeasurableSet A := hA.isClosed.measurableSet
  have hFm (s : 𝕂) : MeasurableSet (F s) :=
    hAm.preimage (euclideanWithHead_continuous N s).measurable
  have hEm : Measurable (fun x : EuclideanSpace 𝕂 (Fin (N+1)) =>
      mismatchHullEnergy x A/4) :=
    (mismatchHullEnergy_measurable A hA).div_const 4
  have hfm : Measurable f := Real.measurable_exp.comp hEm
  have hFubiniIntegrable : Integrable
      (fun z : 𝕂 × (Fin N → 𝕂) =>
        f (toLp 2 (Fin.cons z.1 z.2)))
      (μ.prod (Measure.pi fun _ : Fin N => μ)) := by
    have hm : Measurable (fun z : 𝕂 × (Fin N → 𝕂) =>
        mismatchHullEnergy
          (toLp 2 (Fin.cons z.1 z.2) : EuclideanSpace 𝕂 (Fin (N+1))) A/4) :=
      hEm.comp ((WithLp.measurable_toLp 2 _).comp
        (talagrand_measurable_head_cons N))
    have hb (z : 𝕂 × (Fin N → 𝕂)) :
        mismatchHullEnergy
          (toLp 2 (Fin.cons z.1 z.2) : EuclideanSpace 𝕂 (Fin (N+1))) A/4 ≤
        ((N+1 : ℕ) : ℝ)/4 := by
      exact (div_le_div_of_nonneg_right
        (mismatchHullEnergy_bounds _ A).2 (by norm_num))
    exact integrable_exp_of_bounded_energy _ _ hm _ hb
  have hPFmeas : Measurable (fun s : 𝕂 => ν.real (F s)) := by
    have hS : MeasurableSet
        {z : 𝕂 × EuclideanSpace 𝕂 (Fin N) |
          euclideanWithHead N z.1 z.2 ∈ A} :=
      hAm.preimage (euclideanWithHead_joint_continuous N).measurable
    simpa only [F, Set.preimage_ofPred_eq] using
      (talagrand_fiber_mass_measurable_and_mean μ ν _ hS).1
  have hMass : pA = ∫ s, ν.real (F s) ∂μ := by
    have h := talagrand_product_fiber_mass μ N A hAm
    rw [← talagrandEuclideanProductLaw_real μ (N+1) A hAm] at h
    calc
      pA = ∫ s, (Measure.pi (fun _ : Fin N => μ)).real
          {z : Fin N → 𝕂 |
            euclideanWithHead N s
              (toLp 2 z : EuclideanSpace 𝕂 (Fin N)) ∈ A} ∂μ := h
      _ = ∫ s, ν.real (F s) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with s
        exact (talagrandEuclideanProductLaw_real μ N (F s) (hFm s)).symm
  have hPFint : Integrable (fun s : 𝕂 => ν.real (F s)) μ := by
    apply (integrable_const (1 : ℝ)).mono' hPFmeas.aestronglyMeasurable
    filter_upwards [] with s
    have h0 : 0 ≤ ν.real (F s) := measureReal_nonneg
    have h1 : ν.real (F s) ≤ 1 := by
      calc
        ν.real (F s) ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ _)
        _ = 1 := by simp
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have hpB : 0 < pB := by
    have hle : pA ≤ pB := by
      rw [hMass]
      calc
        (∫ s, ν.real (F s) ∂μ) ≤ ∫ _s : 𝕂, pB ∂μ := by
          apply integral_mono hPFint (integrable_const pB)
          intro s
          apply measureReal_mono (h₂ := measure_ne_top ν _)
          intro y hy
          exact ⟨euclideanWithHead N s y, hy, by ext i; rfl⟩
        _ = pB := by simp
    exact lt_of_lt_of_le hpA hle
  have hJint : Integrable (fun s : 𝕂 =>
      ∫ y, f (euclideanWithHead N s y) ∂ν) μ := by
    have h := hFubiniIntegrable.integral_prod_left
    convert h using 1
    funext s
    exact (talagrandEuclideanProductLaw_integral μ N
      (fun y => f (euclideanWithHead N s y))
      (hfm.comp (euclideanWithHead_continuous N s).measurable))
  have hIntegral : (∫ x, f x ∂talagrandEuclideanProductLaw μ (N+1)) =
      ∫ s, ∫ y, f (euclideanWithHead N s y) ∂ν ∂μ := by
    have h := talagrand_product_integral_fubini μ N f hfm hFubiniIntegrable
    rw [← talagrandEuclideanProductLaw_integral μ (N+1) f hfm] at h
    calc
      (∫ x, f x ∂talagrandEuclideanProductLaw μ (N+1)) =
          ∫ s, ∫ z : Fin N → 𝕂,
            f (euclideanWithHead N s
              (toLp 2 z : EuclideanSpace 𝕂 (Fin N)))
              ∂Measure.pi (fun _ : Fin N => μ) ∂μ := h
      _ = ∫ s, ∫ y, f (euclideanWithHead N s y) ∂ν ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with s
        exact (talagrandEuclideanProductLaw_integral μ N
          (fun y => f (euclideanWithHead N s y))
          (hfm.comp (euclideanWithHead_continuous N s).measurable)).symm
  exact talagrand_compact_moment_step N μ ν A hA hAne pA
    (∫ x, f x ∂talagrandEuclideanProductLaw μ (N+1)) hpA pB hpB rfl
    hPFmeas hMass hJint hIntegral (hBmoment hpB)
    (fun s pF hpF hdef => by
      subst pF
      exact hFmoment s hpF)

#print axioms talagrand_compact_iid_step
end SpectralRadiusUpperTail
