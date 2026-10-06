import SpectralRadiusUpperTail.MarkedNonrealRootMultiset
import SpectralRadiusUpperTail.GaussianMatrixReindexLaw
import SpectralRadiusUpperTail.RealGaussianSubstatIntegrable
import SpectralRadiusUpperTail.RealGaussianActualSimpleSpectrum

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal Matrix Matrix.Norms.Operator

noncomputable def complexExteriorPowerWeight (k : ℕ) (z : ℂ) : ℝ≥0∞ :=
  if 1 < ‖z‖ then ENNReal.ofReal (‖z‖^(2*k)) else 0

theorem complexExteriorPowerWeight_measurable (k : ℕ) : Measurable (complexExteriorPowerWeight k) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_norm)
    ((measurable_norm.pow_const _).ennreal_ofReal) measurable_const

noncomputable def markedNonrealIndexEquiv (m : ℕ) : Fin (m+2) ≃ MarkedNonrealIndex m :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin,markedNonrealCoord_card])

/-- Reindexing and positive variance scaling identify the actual power
statistic with the weighted root count used by the marked-pair atlas. -/
theorem realGaussianUpperNonrealPower_native_lintegral (m k : ℕ) :
    ENNReal.ofReal (∫ a, realGaussianUpperNonrealExteriorPower (m+2) k a
      ∂gaussianMatrixLaw (m+2)) =
      ∫⁻ a : MarkedNonrealIndex m × MarkedNonrealIndex m → ℝ,
        markedNonrealRootWeight m (Matrix.of a.curry)
          (fun z => complexExteriorPowerWeight k ((1/Real.sqrt (m+2 : ℝ)) • z))
            ∂Measure.pi (fun _ => standardNormal) := by
  let c : ℝ := 1/Real.sqrt (m+2 : ℝ)
  let e := markedNonrealIndexEquiv m
  let R := fun a : (Fin (m+2) × Fin (m+2)) → ℝ =>
    fun ij : MarkedNonrealIndex m × MarkedNonrealIndex m => a (e.symm ij.1,e.symm ij.2)
  let g := fun z : ℂ => complexExteriorPowerWeight k (c • z)
  have hc : 0 < c := by dsimp [c]; positivity
  have hg : Measurable g := (complexExteriorPowerWeight_measurable k).comp (by fun_prop)
  have hcur : Measurable (fun a : MarkedNonrealIndex m × MarkedNonrealIndex m → ℝ =>
      Matrix.of a.curry) := by
    change Measurable (realMatrixEntryEquiv (MarkedNonrealIndex m)).symm
    exact (realMatrixEntryEquiv (MarkedNonrealIndex m)).symm.toContinuousLinearEquiv.continuous.measurable
  have hf : Measurable (fun a : MarkedNonrealIndex m × MarkedNonrealIndex m → ℝ =>
      markedNonrealRootWeight m (Matrix.of a.curry) g) :=
    (markedNonrealRootWeight_measurable m g hg).comp hcur
  have ht := lintegral_map (μ := gaussianMatrixLaw (m+2)) hf
    (show Measurable R by dsimp [R]; fun_prop)
  rw [gaussianMatrixLaw_map_reindex e] at ht
  change ENNReal.ofReal (∫ a, realGaussianUpperNonrealExteriorPower (m+2) k a
    ∂gaussianMatrixLaw (m+2))=(∫⁻ a, markedNonrealRootWeight m (Matrix.of a.curry) g
      ∂Measure.pi (fun _ => standardNormal))
  rw [ht,ofReal_integral_eq_lintegral_ofReal
    (realGaussianUpperNonrealExteriorPower_integrable (m+2) k (by omega))
    (Filter.Eventually.of_forall (fun a => (realMatrixUpperNonrealExteriorPower_nonneg_le_total _ k).1))]
  apply lintegral_congr_ae
  filter_upwards [realGaussianMatrix_charpoly_separable_ae (m+2)] with a ha
  have hp : (Matrix.of (R a).curry).charpoly=(Matrix.of a.curry).charpoly :=
    Matrix.charpoly_reindex e (Matrix.of a.curry)
  have hs : (Matrix.of (R a).curry).charpoly.Separable := hp.symm ▸ ha
  rw [markedNonrealRootWeight_eq_roots m _ hs,hp]
  unfold realGaussianUpperNonrealExteriorPower
  rw [show entryMatrix a=Matrix.of a.curry from rfl]
  simpa only [c,g,complexExteriorPowerWeight,Nat.cast_add,Nat.cast_ofNat] using
    realMatrixUpperNonrealExteriorPower_scaled_roots (Matrix.of a.curry) c hc k

#print axioms complexExteriorPowerWeight_measurable
#print axioms realGaussianUpperNonrealPower_native_lintegral
end SpectralRadiusUpperTail
