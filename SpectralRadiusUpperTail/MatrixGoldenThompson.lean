import SpectralRadiusUpperTail.MatrixTraceDyadicPower
import SpectralRadiusUpperTail.AlgebraLieProduct
import SpectralRadiusUpperTail.MatrixNormTransport

namespace SpectralRadiusUpperTail
open Filter Topology
open scoped ComplexOrder Matrix Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
  [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Golden--Thompson, proved from dyadic trace Holder and the actual Lie limit. -/
theorem matrix_golden_thompson (A B : Matrix ι ι 𝕂)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (NormedSpace.exp (A+B)).trace ≤
      RCLike.re (NormedSpace.exp A*NormedSpace.exp B).trace := by
  let F := fun k : ℕ =>
    (NormedSpace.exp (((2^k : ℕ) : ℝ)⁻¹ • A)*
      NormedSpace.exp (((2^k : ℕ) : ℝ)⁻¹ • B))^(2^k)
  have hbound : ∀ k, RCLike.re (F k).trace ≤
      RCLike.re (NormedSpace.exp A*NormedSpace.exp B).trace := by
    intro k
    have hAe : (NormedSpace.exp (((2^k : ℕ) : ℝ)⁻¹ • A)).IsHermitian := by
      have hh : IsSelfAdjoint (((2^k : ℕ) : ℝ)⁻¹ • A) :=
        hA.smul (show IsSelfAdjoint (((2^k : ℕ) : ℝ)⁻¹) from rfl)
      exact hh.exp
    have hBe : (NormedSpace.exp (((2^k : ℕ) : ℝ)⁻¹ • B)).IsHermitian := by
      have hh : IsSelfAdjoint (((2^k : ℕ) : ℝ)⁻¹ • B) :=
        hB.smul (show IsSelfAdjoint (((2^k : ℕ) : ℝ)⁻¹) from rfl)
      exact hh.exp
    have hh := matrix_trace_hermitian_dyadic _ _ hAe hBe k
    rw [algebra_exp_div_pow A (2^k) (by positivity),
      algebra_exp_div_pow B (2^k) (by positivity)] at hh
    exact hh
  have hn : Tendsto (fun k : ℕ => 2^k-1) atTop atTop := by
    apply tendsto_atTop_mono (fun k => ?_) tendsto_id
    change k ≤ 2^k-1
    have hh := k.lt_two_pow_self
    omega
  have hlim : Tendsto F atTop (𝓝 (NormedSpace.exp (A+B))) := by
    have hh := (algebra_lie_product_tendsto A B).comp hn
    have he : ∀ k : ℕ, 2^k-1+1 = 2^k := fun k => Nat.sub_add_cancel (by
      have hp : 0 < (2 : ℕ)^k := by positivity
      omega)
    simpa only [Function.comp_def,he] using hh
  let tr : Matrix ι ι 𝕂 →L[𝕂] 𝕂 :=
    (Matrix.traceLinearMap ι 𝕂 𝕂).toContinuousLinearMap
  have hc : Continuous (fun M : Matrix ι ι 𝕂 => RCLike.re M.trace) :=
    RCLike.continuous_re.comp tr.continuous
  exact le_of_tendsto ((hc.tendsto _).comp hlim) (Eventually.of_forall hbound)

#print axioms matrix_golden_thompson
end SpectralRadiusUpperTail
