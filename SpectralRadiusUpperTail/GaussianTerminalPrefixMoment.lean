import SpectralRadiusUpperTail.TerminalCoefficientMask
import SpectralRadiusUpperTail.GaussianRowPrefixMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Uniform exponential-square control of every actual history target on the
same terminal coupled-row law used by the martingale. -/
theorem gaussianTerminalTarget_squareExp (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (τ : ℝ) (hτ : 0 < τ) (hexp : Integrable (fun x : 𝕂 => Real.exp (τ*‖x‖^2)) μ)
    (v : ℕ → 𝕂) (N : ℕ) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (a : ℝ) (ha : 0 < a) (t : 𝕂) (K : ℝ) (ht : ‖t‖ ≤ K) (n : ℕ) (hn : n ≤ N) :
    let c := rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)
    let Γ := gaussianSequentialRowLaw μ v a N t N
    0 < c ∧ Integrable (fun x => Real.exp ((c/2)*‖gaussianTerminalTarget v N t n x‖^2)) Γ ∧
      (∫ x, Real.exp ((c/2)*‖gaussianTerminalTarget v N t n x‖^2) ∂Γ) ≤
        2*Real.exp ((K^2+1)/a+c*K^2) := by
  let c := rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)
  let Γ := gaussianSequentialRowLaw μ v a N t N
  let w := terminalCoefficientMask v N n
  let f := fun z : Fin N → 𝕂 => Real.exp ((c/2)*‖t-∑ i, w i*z i‖^2)
  have hX : MemLp (fun x : 𝕂 => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ τ hτ hexp 2)
  have hsource := gaussianSequentialRowLaw_source μ hX hm hvar v N hv a ha t
  have hproj : Measurable (coordinateVector (@Prod.fst 𝕂 𝕂) N) :=
    measurable_coordinateVector Prod.fst measurable_fst N
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hmoment := gaussianFiniteRowLaw_shifted_sum_squareExp μ hm hvar τ hτ hexp
    (fun i : Fin N => v i.val) w hv (terminalCoefficientMask_energy v N n hv) a ha t K ht
  have hi : Integrable f (Γ.map (coordinateVector Prod.fst N)) := by
    rw [hsource]
    exact hmoment.2.1
  have heq : (fun x => Real.exp ((c/2)*‖gaussianTerminalTarget v N t n x‖^2)) =
      f ∘ coordinateVector Prod.fst N := by
    funext x
    rw [gaussianTerminalTarget_eq_mask v N t n hn x]
    rfl
  refine ⟨hmoment.1, ?_, ?_⟩
  · rw [heq]
    exact hi.comp_measurable hproj
  · rw [heq]
    have he := integral_map (μ := Γ) hproj.aemeasurable hf.aestronglyMeasurable
    rw [hsource] at he
    exact he.symm.le.trans hmoment.2.2

#print axioms gaussianTerminalTarget_squareExp
end SpectralRadiusUpperTail
