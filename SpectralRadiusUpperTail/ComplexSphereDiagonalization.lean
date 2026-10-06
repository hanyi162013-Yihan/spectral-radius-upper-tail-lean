import SpectralRadiusUpperTail.HaarSphereIsometry
import SpectralRadiusUpperTail.HermitianEigenbasisEnergy
import SpectralRadiusUpperTail.ComplexDiagonalSphereIntegral
import SpectralRadiusUpperTail.SphereQuadraticIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal ComplexOrder MatrixOrder

lemma complex_sphere_integral_diagonalization (n : ℕ) (hn : 0 < n)
    (c : ℝ) (hc : 0 ≤ c) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) :
    ENNReal.ofReal (sphereQuadraticIntegral ℂ n c H) =
      complexDiagonalSphereIntegral n c hH.isHermitian.eigenvalues := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (Real.exp (-c*(inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).re))
  have hF : Measurable F := by dsimp [F]; fun_prop
  let U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
    { hH.isHermitian.eigenvectorBasis.repr.symm.toLinearEquiv.restrictScalars ℝ with
      norm_map' := hH.isHermitian.eigenvectorBasis.repr.symm.norm_map }
  have he := haarSphere_lintegral_isometry U F hF
  rw [sphereQuadraticIntegral_lintegral ℂ n hn c hc H hH]
  change (∫⁻ v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1,
    F v.val ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))) = _
  rw [← he]
  apply lintegral_congr
  intro v
  convert! congrArg (fun t : ℝ => ENNReal.ofReal (Real.exp (-c*t)))
    (hermitian_eigenbasis_energy H hH.isHermitian v.val) using 1

#print axioms complex_sphere_integral_diagonalization
end SpectralRadiusUpperTail
