import SpectralRadiusUpperTail.MarkedNonrealGaussianCalibration
import SpectralRadiusUpperTail.MarkedNonrealDensityScaling
import SpectralRadiusUpperTail.MarkedNonrealPowerExpectationBridge
import SpectralRadiusUpperTail.RealGinibreWeightedNonrealIntegrability

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal Matrix Matrix.Norms.Operator

noncomputable def realGaussianNonrealWeightConstant : ℝ :=
  8*Real.pi^2/markedNonrealPairReferenceMass.toReal

theorem realGaussianNonrealWeightConstant_pos : 0 < realGaussianNonrealWeightConstant := by
  have h : 0 < markedNonrealPairReferenceMass.toReal :=
    ENNReal.toReal_pos markedNonrealPairReferenceMass_pos.ne' markedNonrealPairReferenceMass_ne_top
  unfold realGaussianNonrealWeightConstant
  positivity

theorem realGaussianNonrealWeightConstant_ofReal :
    ENNReal.ofReal realGaussianNonrealWeightConstant=
      ENNReal.ofReal (8*Real.pi^2)/markedNonrealPairReferenceMass := by
  have h : 0 < markedNonrealPairReferenceMass.toReal :=
    ENNReal.toReal_pos markedNonrealPairReferenceMass_pos.ne' markedNonrealPairReferenceMass_ne_top
  rw [realGaussianNonrealWeightConstant,ENNReal.ofReal_div_of_pos h,
    ENNReal.ofReal_toReal markedNonrealPairReferenceMass_ne_top]

theorem realGinibreUpperWeightedIntegral_le (n k : ℕ) (hn : 0 < n) :
    (∫⁻ z : ℂ in {z | 0 < z.im},
      ENNReal.ofReal (realGinibreNonrealDensityAt n z)*complexExteriorPowerWeight k z) ≤
      ENNReal.ofReal (∫ z : ℂ in {z | 1 < ‖z‖},
        ‖z‖^(2*k)*realGinibreNonrealDensityAt n z) := by
  let S : Set ℂ := {z | 1 < ‖z‖}
  let f := fun z : ℂ => ENNReal.ofReal (‖z‖^(2*k)*realGinibreNonrealDensityAt n z)
  have hp (z : ℂ) : ENNReal.ofReal (realGinibreNonrealDensityAt n z)*
      complexExteriorPowerWeight k z=S.indicator f z := by
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
      change 1 < ‖z‖ at hz
      rw [complexExteriorPowerWeight,if_pos hz]
      dsimp only [f]
      rw [ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _),mul_comm]
    · rw [Set.indicator_of_notMem hz]
      change ¬1 < ‖z‖ at hz
      simp [complexExteriorPowerWeight,hz]
  calc
    _ ≤ ∫⁻ z : ℂ, ENNReal.ofReal (realGinibreNonrealDensityAt n z)*
        complexExteriorPowerWeight k z := setLIntegral_le_lintegral _ _
    _ = ∫⁻ z : ℂ in S, f z := by
      simp_rw [hp]
      rw [lintegral_indicator (measurableSet_lt measurable_const measurable_norm)]
    _ = _ := realGinibreNonrealDensityAt_weighted_lintegral n k hn

/-- The actual iid real Gaussian nonreal power statistic has the desired
one-point upper bound up to a fixed constant times the dimension. -/
theorem realGaussianNonreal_weighted_linear_upper_succ
    (m k : ℕ) (hm : 0 < m) :
    2*(∫ a, realGaussianUpperNonrealExteriorPower (m+2) k a ∂gaussianMatrixLaw (m+2)) ≤
      realGaussianNonrealWeightConstant*(m+2 : ℝ)*
        (∫ z : ℂ in {z | 1 < ‖z‖}, ‖z‖^(2*k)*realGinibreNonrealDensityAt (m+2) z) := by
  let J := ∫ z : ℂ in {z | 1 < ‖z‖}, ‖z‖^(2*k)*realGinibreNonrealDensityAt (m+2) z
  have hJ : 0 ≤ J := setIntegral_nonneg (measurableSet_lt measurable_const measurable_norm)
    (fun z hz => mul_nonneg (pow_nonneg (norm_nonneg _) _)
      (realGinibreNonrealDensityAt_bound (m+2) z hz.le).1)
  have h := markedNonrealGaussian_weighted_upper m hm
    (fun z => complexExteriorPowerWeight k ((1/Real.sqrt (m+2 : ℝ)) • z))
    ((complexExteriorPowerWeight_measurable k).comp (by fun_prop))
  rw [← realGaussianUpperNonrealPower_native_lintegral m k,
    markedNonrealPairTestIntegral_scale m _ (complexExteriorPowerWeight_measurable k)] at h
  have hu := realGinibreUpperWeightedIntegral_le (m+2) k (by omega)
  have hC := realGaussianNonrealWeightConstant_pos
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
    (mul_nonneg hC.le (by positivity : (0 : ℝ) ≤ m+2)) hJ)).mp
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat]
  calc
    _ ≤ 2*(((m+2 : ℕ)/markedNonrealPairReferenceMass)*
        (ENNReal.ofReal (4*Real.pi^2)*
          ∫⁻ z : ℂ in {z | 0 < z.im}, ENNReal.ofReal (realGinibreNonrealDensityAt (m+2) z)*
            complexExteriorPowerWeight k z)) := mul_le_mul le_rfl h zero_le zero_le
    _ ≤ 2*(((m+2 : ℕ)/markedNonrealPairReferenceMass)*
        (ENNReal.ofReal (4*Real.pi^2)*ENNReal.ofReal J)) := by gcongr
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC.le (by positivity : (0 : ℝ) ≤ m+2)),
        ENNReal.ofReal_mul hC.le,realGaussianNonrealWeightConstant_ofReal]
      have hp : ENNReal.ofReal (8*Real.pi^2)=2*ENNReal.ofReal (4*Real.pi^2) := by
        rw [← ENNReal.ofReal_ofNat,← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      rw [hp]
      have hnR : ENNReal.ofReal (m+2 : ℝ)=((m+2 : ℕ) : ℝ≥0∞) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using ENNReal.ofReal_natCast (m+2)
      rw [hnR]
      simp only [div_eq_mul_inv]
      ac_rfl

theorem realGaussianNonreal_weighted_linear_upper
    (n k : ℕ) (hn : 3 ≤ n) :
    2*(∫ a, realGaussianUpperNonrealExteriorPower n k a ∂gaussianMatrixLaw n) ≤
      realGaussianNonrealWeightConstant*(n : ℝ)*
        (∫ z : ℂ in {z | 1 < ‖z‖}, ‖z‖^(2*k)*realGinibreNonrealDensityAt n z) := by
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+2 := ⟨n-2,by omega⟩
  simpa only [Nat.cast_add,Nat.cast_ofNat] using
    realGaussianNonreal_weighted_linear_upper_succ m k (by omega)

#print axioms realGaussianNonrealWeightConstant_pos
#print axioms realGaussianNonrealWeightConstant_ofReal
#print axioms realGinibreUpperWeightedIntegral_le
#print axioms realGaussianNonreal_weighted_linear_upper_succ
#print axioms realGaussianNonreal_weighted_linear_upper
end SpectralRadiusUpperTail
