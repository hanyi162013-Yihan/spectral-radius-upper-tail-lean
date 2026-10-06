import SpectralRadiusUpperTail.RegularizedConvexSlopes
import SpectralRadiusUpperTail.MonotonePrimitiveConvex

namespace SpectralRadiusUpperTail
open MeasureTheory Set

noncomputable def regularizedLogConvex₁ (τ s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..s, regularizedConvexSlope₁ τ t

noncomputable def regularizedLogConvex₂ (τ s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..s, regularizedConvexSlope₂ τ t

lemma regularizedLog_hasDerivAt (τ x : ℝ) (hτ : 0 < τ) :
    HasDerivAt (fun s : ℝ => Real.log (s^2+τ^2)) (regularizedLogSlope τ x) x := by
  have hd : x^2+τ^2 ≠ 0 := ne_of_gt (by positivity)
  convert (((hasDerivAt_id x).pow 2).add_const (τ^2)).log hd using 1 <;>
    simp [regularizedLogSlope] <;> ring

lemma regularizedLog_convex_decomposition (τ s : ℝ) (hτ : 0 < τ) :
    Real.log (s^2+τ^2) = 2*Real.log τ+regularizedLogConvex₁ τ s-regularizedLogConvex₂ τ s := by
  have h1 := regularizedConvexSlope₁_continuous τ hτ
  have h2 := regularizedConvexSlope₂_continuous τ hτ
  have hsub : regularizedLogConvex₁ τ s-regularizedLogConvex₂ τ s =
      ∫ t in (0 : ℝ)..s, regularizedLogSlope τ t := by
    rw [regularizedLogConvex₁, regularizedLogConvex₂,
      ← intervalIntegral.integral_sub (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)]
    congr 1
    funext t
    exact regularizedConvexSlopes_sub τ t
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ uIcc (0 : ℝ) s) => regularizedLog_hasDerivAt τ x hτ)
    ((regularizedLogSlope_continuous τ hτ).intervalIntegrable 0 s)
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_add, Real.log_pow, Nat.cast_ofNat] at hi
  linarith

lemma regularizedLogConvex_zero (τ : ℝ) :
    regularizedLogConvex₁ τ 0 = 0 ∧ regularizedLogConvex₂ τ 0 = 0 := by
  simp [regularizedLogConvex₁, regularizedLogConvex₂]

lemma regularizedLogConvex₁_properties (τ : ℝ) (hτ : 0 < τ) :
    ConvexOn ℝ (Ici 0) (regularizedLogConvex₁ τ) ∧
    MonotoneOn (regularizedLogConvex₁ τ) (Ici 0) ∧
    LipschitzOnWith (Real.toNNReal (1/τ)) (regularizedLogConvex₁ τ) (Ici 0) := by
  apply monotone_primitive_convex_package _ (regularizedConvexSlope₁_continuous τ hτ)
    (regularizedConvexSlope₁_monotone τ hτ)
  intro x hx
  simpa only [Real.coe_toNNReal _ (by positivity : 0 ≤ 1/τ)] using
    (regularizedConvexSlopes_bounds τ x hτ hx).1

lemma regularizedLogConvex₂_properties (τ : ℝ) (hτ : 0 < τ) :
    ConvexOn ℝ (Ici 0) (regularizedLogConvex₂ τ) ∧
    MonotoneOn (regularizedLogConvex₂ τ) (Ici 0) ∧
    LipschitzOnWith (Real.toNNReal (1/τ)) (regularizedLogConvex₂ τ) (Ici 0) := by
  apply monotone_primitive_convex_package _ (regularizedConvexSlope₂_continuous τ hτ)
    (regularizedConvexSlope₂_monotone τ hτ)
  intro x hx
  simpa only [Real.coe_toNNReal _ (by positivity : 0 ≤ 1/τ)] using
    (regularizedConvexSlopes_bounds τ x hτ hx).2

#print axioms regularizedLog_hasDerivAt
#print axioms regularizedLog_convex_decomposition
#print axioms regularizedLogConvex_zero
#print axioms regularizedLogConvex₁_properties
#print axioms regularizedLogConvex₂_properties
end SpectralRadiusUpperTail
