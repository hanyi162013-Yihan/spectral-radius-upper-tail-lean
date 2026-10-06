import SpectralRadiusUpperTail.NormalizedSingularObservable
import SpectralRadiusUpperTail.IidSerialMatrix
import SpectralRadiusUpperTail.SphereResidualWeight

namespace SpectralRadiusUpperTail
open scoped NNReal

lemma regularized_convex_observable₁ (n : ℕ) (hn : 0 < n) (z : ℂ) (τ : ℝ) (hτ : 0 < τ) :
    ConvexOn ℝ Set.univ (normalizedSingularObservable n z (regularizedLogConvex₁ τ)) ∧
    LipschitzWith (Real.toNNReal (1/τ)/(n : ℝ≥0))
      (normalizedSingularObservable n z (regularizedLogConvex₁ τ)) := by
  obtain ⟨hc, hm, hl⟩ := regularizedLogConvex₁_properties τ hτ
  exact ⟨normalizedSingularObservable_convex n z _ hc hm,
    normalizedSingularObservable_lipschitz n hn z _ hc hm _ hl⟩

lemma regularized_convex_observable₂ (n : ℕ) (hn : 0 < n) (z : ℂ) (τ : ℝ) (hτ : 0 < τ) :
    ConvexOn ℝ Set.univ (normalizedSingularObservable n z (regularizedLogConvex₂ τ)) ∧
    LipschitzWith (Real.toNNReal (1/τ)/(n : ℝ≥0))
      (normalizedSingularObservable n z (regularizedLogConvex₂ τ)) := by
  obtain ⟨hc, hm, hl⟩ := regularizedLogConvex₂_properties τ hτ
  exact ⟨normalizedSingularObservable_convex n z _ hc hm,
    normalizedSingularObservable_lipschitz n hn z _ hc hm _ hl⟩

lemma regularizedResidualLogDet_convex_decomposition (n : ℕ) (hn : 0 < n)
    (z : ℂ) (τ : ℝ) (hτ : 0 < τ) (x : Fin n → Fin n → ℂ) :
    regularizedResidualLogDet x z (τ^2)/(n : ℝ) = 2*Real.log τ+
      normalizedSingularObservable n z (regularizedLogConvex₁ τ)
        (WithLp.toLp 2 (serialMatrixEntries x))-
      normalizedSingularObservable n z (regularizedLogConvex₂ τ)
        (WithLp.toLp 2 (serialMatrixEntries x)) := by
  have hh := normalized_gram_regularized_logDet_convex_split hn (normalizedArray x-z • 1) τ hτ
  simpa only [normalizedSingularObservable, matrixSingularSum, euclideanResidualMatrix_serial,
    regularizedResidualLogDet, spectralResidualGram] using! hh

#print axioms regularized_convex_observable₁
#print axioms regularized_convex_observable₂
#print axioms regularizedResidualLogDet_convex_decomposition
end SpectralRadiusUpperTail
