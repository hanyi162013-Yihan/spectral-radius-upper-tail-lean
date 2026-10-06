import SpectralRadiusUpperTail.RealSchurMixedAngularJacobian
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- The lower-block entries of an angular orthogonal frame, with the
sign chosen so its derivative at the identity is the identity. For the
two-block `(1,m)` shape these are the complementary coordinates of the
marked unit eigenvector. -/
noncomputable def realSchurMixedAngularProjection
    {m : ℕ} (s : Fin m → ℕ)
    (w : RealSchurMixedOrbitIndex s → ℝ) :
      RealSchurMixedOrbitIndex s → ℝ :=
  -realSchurMixedLowerProjection s (realSchurMixedAngularFrame s w)

theorem realSchurMixedAngularProjection_hasStrictFDerivAt_zero
    {m : ℕ} (s : Fin m → ℕ) :
    HasStrictFDerivAt (realSchurMixedAngularProjection s)
      (ContinuousLinearMap.id ℝ (RealSchurMixedOrbitIndex s → ℝ)) 0 := by
  have hE := Ginibre.hasStrictFDerivAt_exp_linear
    (realSchurMixedSkewCLM s)
  have hL :
      ((-realSchurMixedLowerProjection s).comp
        (realSchurMixedSkewCLM s)) =
      (ContinuousLinearMap.id ℝ (RealSchurMixedOrbitIndex s → ℝ)) := by
    ext w q
    change -(realSchurMixedLowerProjection s
      (realSchurMixedSkewEmbed s w)) q = w q
    rw [realSchurMixedLowerProjection_skewEmbed]
    simp
  have h := (-realSchurMixedLowerProjection s).hasStrictFDerivAt.comp 0 hE
  change HasStrictFDerivAt (realSchurMixedAngularProjection s)
    ((-realSchurMixedLowerProjection s).comp
      (realSchurMixedSkewCLM s)) 0 at h
  rwa [hL] at h

/-- A canonical local angular coordinate chart, independent of all
Schur diagonal and upper-block entries. -/
noncomputable def realSchurMixedAngularProjectionChart
    {m : ℕ} (s : Fin m → ℕ) :
    OpenPartialHomeomorph
      (RealSchurMixedOrbitIndex s → ℝ)
      (RealSchurMixedOrbitIndex s → ℝ) :=
  (show HasStrictFDerivAt (realSchurMixedAngularProjection s)
      (ContinuousLinearEquiv.refl ℝ (RealSchurMixedOrbitIndex s → ℝ) :
        (RealSchurMixedOrbitIndex s → ℝ) →L[ℝ]
          (RealSchurMixedOrbitIndex s → ℝ)) 0 from
    realSchurMixedAngularProjection_hasStrictFDerivAt_zero s).toOpenPartialHomeomorph
      (realSchurMixedAngularProjection s)

theorem realSchurMixedAngularProjectionChart_zero_mem_source
    {m : ℕ} (s : Fin m → ℕ) :
    0 ∈ (realSchurMixedAngularProjectionChart s).source :=
  (show HasStrictFDerivAt (realSchurMixedAngularProjection s)
      (ContinuousLinearEquiv.refl ℝ (RealSchurMixedOrbitIndex s → ℝ) :
        (RealSchurMixedOrbitIndex s → ℝ) →L[ℝ]
          (RealSchurMixedOrbitIndex s → ℝ)) 0 from
    realSchurMixedAngularProjection_hasStrictFDerivAt_zero s).mem_toOpenPartialHomeomorph_source

#print axioms realSchurMixedAngularProjection_hasStrictFDerivAt_zero
#print axioms realSchurMixedAngularProjectionChart_zero_mem_source
end SpectralRadiusUpperTail
