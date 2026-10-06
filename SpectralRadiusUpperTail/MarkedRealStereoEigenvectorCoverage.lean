import SpectralRadiusUpperTail.MarkedRealColumnUpper
import SpectralRadiusUpperTail.MarkedRealStereoCoverage
import SpectralRadiusUpperTail.MarkedRealStereoMatrixMap

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Every positively oriented unit eigenvector is represented by the
explicit Schur map, together with the correct scalar eigenvalue. -/
theorem markedRealStereo_positive_unit_eigenvector_coverage (m : ℕ)
    (A : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (v : RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ)
    (hunit : ∑ i, (v i)^2 = 1) (hpos : 0 < v (markedRealFirstCoordinate m))
    (z : ℝ) (hAv : A *ᵥ v = z • v) :
    ∃ p : RealSchurMixedTangent (markedRealTwoBlockSizes m),
      p.1 ∈ markedRealStereoSource m ∧ markedRealScalar m p.2.val = z ∧
        markedRealStereoMatrixMap m p = A := by
  obtain ⟨u,hu,hcol⟩ := markedRealStereoFrame_covers_positive_unit_column m v hunit hpos
  let w : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ :=
    fun q => u ((markedRealOrbitEquiv m).symm q)
  have hw : markedRealStereoParameterCLM m w = u := by
    funext i
    change u ((markedRealOrbitEquiv m).symm (markedRealOrbitEquiv m i)) = u i
    rw [Equiv.symm_apply_apply]
  have hsource : w ∈ markedRealStereoSource m := by
    change markedRealStereoParameterCLM m w ⬝ᵥ markedRealStereoParameterCLM m w < 1
    rwa [hw]
  have hQcol : (fun i => markedRealStereoNativeFrame m w i
      (markedRealFirstCoordinate m)) = v := by
    unfold markedRealStereoNativeFrame
    rw [hw]
    exact funext hcol
  have hAQ : A *ᵥ (fun i => markedRealStereoNativeFrame m w i
      (markedRealFirstCoordinate m)) =
      z • (fun i => markedRealStereoNativeFrame m w i (markedRealFirstCoordinate m)) := by
    rwa [hQcol]
  obtain ⟨S,hS,hA⟩ := markedReal_orthogonal_eigenColumn_upper m A
    (markedRealStereoNativeFrame m w) (markedRealStereoNativeFrame_orthogonal m w) z hAQ
  exact ⟨(w,S),hsource,hS,hA.symm⟩

#print axioms markedRealStereo_positive_unit_eigenvector_coverage
end SpectralRadiusUpperTail
