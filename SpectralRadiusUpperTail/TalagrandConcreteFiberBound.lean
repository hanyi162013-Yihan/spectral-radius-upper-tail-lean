import SpectralRadiusUpperTail.TalagrandFiberCompactness
import SpectralRadiusUpperTail.TalagrandEnergyIntegrable
import SpectralRadiusUpperTail.TalagrandPositiveFiberStep
import SpectralRadiusUpperTail.TalagrandZeroFiberStep
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂]

/-- The inner integral estimate for one concrete head fiber. The two
lower-dimensional exponential moment bounds are supplied as induction
hypotheses; all geometry, measurability, Hölder and zero-fiber handling
are discharged here. -/
theorem talagrand_concrete_fiber_bound
    (N : ℕ)
    [MeasurableSpace (EuclideanSpace 𝕂 (Fin N))]
    [BorelSpace (EuclideanSpace 𝕂 (Fin N))]
    [MeasurableSpace (EuclideanSpace 𝕂 (Fin (N+1)))]
    [BorelSpace (EuclideanSpace 𝕂 (Fin (N+1)))]
    (ν : Measure (EuclideanSpace 𝕂 (Fin N))) [IsProbabilityMeasure ν]
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1))))
    (hA : IsCompact A) (hAne : A.Nonempty) (s : 𝕂)
    (pB : ℝ) (hpB : 0 < pB)
    (hpBdef : pB = ν.real (euclideanCoordinateTail N '' A))
    (hBmoment : (∫ y,
      Real.exp (mismatchHullEnergy y (euclideanCoordinateTail N '' A)/4) ∂ν) ≤ 1/pB)
    (hFmoment : ∀ pF : ℝ, 0 < pF →
      pF = ν.real {y : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s y ∈ A} →
      (∫ y, Real.exp (mismatchHullEnergy y
        {z : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s z ∈ A}/4) ∂ν) ≤ 1/pF) :
    let pF := ν.real {y : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s y ∈ A}
    let a := pF/pB
    (∫ y, Real.exp
      (mismatchHullEnergy (euclideanWithHead N s y) A/4) ∂ν) ≤
      (1/pB)*Real.exp
        (-talagrandWeight a*Real.log a+(1-talagrandWeight a)^2/4) := by
  let B := euclideanCoordinateTail N '' A
  let F : Set (EuclideanSpace 𝕂 (Fin N)) :=
    {y | euclideanWithHead N s y ∈ A}
  let pF := ν.real F
  let a := pF/pB
  let u := fun y : EuclideanSpace 𝕂 (Fin N) => euclideanWithHead N s y
  let d := fun y : EuclideanSpace 𝕂 (Fin N) => mismatchHullEnergy (u y) A/4
  let f := fun y : EuclideanSpace 𝕂 (Fin N) => mismatchHullEnergy y F/4
  let g := fun y : EuclideanSpace 𝕂 (Fin N) => mismatchHullEnergy y B/4
  change (∫ y, Real.exp (d y) ∂ν) ≤
    (1/pB)*Real.exp
      (-talagrandWeight a*Real.log a+(1-talagrandWeight a)^2/4)
  have hu : Measurable u := (euclideanWithHead_continuous N s).measurable
  have hBcompact : IsCompact B := projectedTarget_compact N A hA
  have hFcompact : IsCompact F := by
    let x : EuclideanSpace 𝕂 (Fin (N+1)) := euclideanWithHead N s 0
    have h := matchingHeadFiber_compact N x A hA
    simpa [F, x, matchingHeadFiber, euclideanWithHead] using h
  have hd : Measurable d :=
    ((mismatchHullEnergy_measurable A hA).comp hu).div_const 4
  have hf : Measurable f := (mismatchHullEnergy_measurable F hFcompact).div_const 4
  have hg : Measurable g := (mismatchHullEnergy_measurable B hBcompact).div_const 4
  have hdC (y) : d y ≤ ((N+1 : ℕ) : ℝ)/4 := by
    dsimp [d]
    exact (div_le_div_of_nonneg_right (mismatchHullEnergy_bounds (u y) A).2 (by norm_num))
  have hfC (y) : f y ≤ (N : ℝ)/4 := by
    dsimp [f]
    exact (div_le_div_of_nonneg_right (mismatchHullEnergy_bounds y F).2 (by norm_num))
  have hgC (y) : g y ≤ (N : ℝ)/4 := by
    dsimp [g]
    exact (div_le_div_of_nonneg_right (mismatchHullEnergy_bounds y B).2 (by norm_num))
  have hdInt := integrable_exp_of_bounded_energy ν d hd _ hdC
  have hfInt := integrable_exp_of_bounded_energy ν f hf _ hfC
  have hgInt := integrable_exp_of_bounded_energy ν g hg _ hgC
  have hFsubB : F ⊆ B := by
    intro y hy
    refine ⟨euclideanWithHead N s y, hy, ?_⟩
    ext i
    rfl
  have hpF0 : 0 ≤ pF := measureReal_nonneg
  have hpFle : pF ≤ pB := by
    rw [hpBdef]
    exact measureReal_mono hFsubB
  have ha0 : 0 ≤ a := div_nonneg hpF0 hpB.le
  have ha1 : a ≤ 1 := (div_le_one hpB).mpr hpFle
  have htail (y : EuclideanSpace 𝕂 (Fin N)) :
      euclideanCoordinateTail N (u y) = y := by
    ext i
    rfl
  have hfiber (y : EuclideanSpace 𝕂 (Fin N)) :
      matchingHeadFiber N (u y) A = F := by
    rfl
  by_cases hpFpos : 0 < pF
  · have haPos : 0 < a := div_pos hpFpos hpB
    have hFne : F.Nonempty := by
      by_contra hnil
      have hnil' : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hnil
      simp [pF, hnil'] at hpFpos
    have hθ := talagrandWeight_mem a ha0 ha1
    have hmixInt := integrable_exp_geometric_mix ν f g hf hg
      ((N : ℝ)/4) (talagrandWeight a) hfC hgC hθ.1 hθ.2
    have hpoint (y : EuclideanSpace 𝕂 (Fin N)) :
        d y ≤ talagrandWeight a*f y+
          (1-talagrandWeight a)*g y+
          (1-talagrandWeight a)^2/4 := by
      have hFhere : {z : EuclideanSpace 𝕂 (Fin N) |
          euclideanWithHead N ((u y) 0) z ∈ A}.Nonempty := by
        change F.Nonempty
        exact hFne
      have hh := mismatchHullEnergy_fiber_interpolation N (u y) A
        hFhere
        (talagrandWeight a) (1-talagrandWeight a)
        hθ.1 (by linarith) (by ring)
      change mismatchHullEnergy (u y) A ≤
        talagrandWeight a*mismatchHullEnergy
          (euclideanCoordinateTail N (u y)) (matchingHeadFiber N (u y) A) +
        (1-talagrandWeight a)*mismatchHullEnergy
          (euclideanCoordinateTail N (u y)) B+
        (1-talagrandWeight a)^2 at hh
      rw [htail y, hfiber y] at hh
      dsimp [d, f, g]
      linarith
    have hpFa : pB*a = pF := by
      dsimp [a]
      field_simp
    have hFm : (∫ y, Real.exp (f y) ∂ν) ≤ 1/(pB*a) := by
      have h := hFmoment pF hpFpos rfl
      simpa only [f, F, ← hpFa] using h
    have hBm : (∫ y, Real.exp (g y) ∂ν) ≤ 1/pB := by
      simpa only [g, B] using hBmoment
    exact talagrand_positive_fiber_step ν d f g hf hg hdInt hfInt hgInt
      pB a hpB haPos ha1 hmixInt hpoint hFm hBm
  · have hpFzero : pF = 0 := le_antisymm (le_of_not_gt hpFpos) hpF0
    have hazero : a = 0 := by simp [a, hpFzero]
    have hpoint (y : EuclideanSpace 𝕂 (Fin N)) : d y ≤ g y+1/4 := by
      have hh := mismatchHullEnergy_projection N (u y) A hAne
      rw [htail y] at hh
      dsimp [d, g]
      linarith
    have hBm : (∫ y, Real.exp (g y) ∂ν) ≤ 1/pB := by
      simpa only [g, B] using hBmoment
    rw [hazero]
    exact talagrand_zero_fiber_step ν d g
      hdInt hgInt pB hpoint hBm

#print axioms talagrand_concrete_fiber_bound
end SpectralRadiusUpperTail
