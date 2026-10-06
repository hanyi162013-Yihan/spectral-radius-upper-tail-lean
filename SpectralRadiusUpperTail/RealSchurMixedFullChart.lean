import SpectralRadiusUpperTail.RealSchurMixedFullTangent
import Ginibre.ExpConjugation
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator RightActions

noncomputable def realSchurMixedSkewTangentCLM
    {m : ℕ} (s : Fin m → ℕ) :
    RealSchurMixedTangent s →L[ℝ]
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => realSchurMixedSkewEmbed s x.1
    map_add' := fun x y => realSchurMixedSkewEmbed_add s x.1 y.1
    map_smul' := fun a x => realSchurMixedSkewEmbed_smul s a x.1 }

noncomputable def realSchurMixedUpperTangentCLM
    {m : ℕ} (s : Fin m → ℕ) :
    RealSchurMixedTangent s →L[ℝ]
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => x.2.val
    map_add' := by intro _ _; rfl
    map_smul' := by intro _ _; rfl }

/-- Actual local mixed-block Schur coordinates. The angular parameter is
exponentiated to an orthogonal matrix; the second parameter varies all
block-upper entries, including the full diagonal blocks. -/
noncomputable def realSchurMixedExpCoordinates
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x : RealSchurMixedTangent s) :
    Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
  NormedSpace.exp (realSchurMixedSkewTangentCLM s x) *
    (T + realSchurMixedUpperTangentCLM s x) *
      NormedSpace.exp (-realSchurMixedSkewTangentCLM s x)

theorem realSchurMixedExpCoordinates_zero
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    realSchurMixedExpCoordinates s T 0 = T := by
  simp [realSchurMixedExpCoordinates]

theorem realSchurMixedExpCoordinates_eq_conjugation
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x : RealSchurMixedTangent s) :
    realSchurMixedExpCoordinates s T x =
      realSchurMixedAngularFrame s x.1 * (T+x.2.val) *
        (realSchurMixedAngularFrame s x.1)ᵀ := by
  unfold realSchurMixedExpCoordinates realSchurMixedAngularFrame
  have hskew : ((realSchurMixedSkewTangentCLM s) x)ᵀ =
      -((realSchurMixedSkewTangentCLM s) x) :=
    realSchurMixedSkewEmbed_transpose s x.1
  rw [← hskew, Matrix.exp_transpose]
  rfl

/-- The strict derivative of the actual coordinate map is the previously
proved full tangent equivalence. -/
theorem realSchurMixedExpCoordinates_hasStrictFDerivAt
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    HasStrictFDerivAt (realSchurMixedExpCoordinates s T)
      (LinearMap.toContinuousLinearMap (realSchurMixedTangentMap s T)) 0 := by
  convert! (Ginibre.hasStrictFDerivAt_exp_conjugation T
    (realSchurMixedSkewTangentCLM s)
    (realSchurMixedUpperTangentCLM s)) using 1
  apply ContinuousLinearMap.ext
  intro x
  change x.2.val + (realSchurMixedSkewEmbed s x.1 * T -
    T * realSchurMixedSkewEmbed s x.1) =
      x.2.val + realSchurMixedSkewEmbed s x.1 * T -
        T * realSchurMixedSkewEmbed s x.1
  abel

/-- The inverse function theorem supplies a genuine open local real-Schur
chart at every separated mixed-block configuration. -/
noncomputable def realSchurMixedLocalChart
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data) :
    OpenPartialHomeomorph (RealSchurMixedTangent (fun i => (B i).size))
      (Matrix (RealSchurMixedCoord (fun i => (B i).size))
        (RealSchurMixedCoord (fun i => (B i).size)) ℝ) :=
  (show HasStrictFDerivAt
      (realSchurMixedExpCoordinates (fun i => (B i).size) T)
      (realSchurMixedTangentEquiv B T hT hdiag hsep :
        RealSchurMixedTangent (fun i => (B i).size) →L[ℝ]
          Matrix (RealSchurMixedCoord (fun i => (B i).size))
            (RealSchurMixedCoord (fun i => (B i).size)) ℝ) 0 from
    realSchurMixedExpCoordinates_hasStrictFDerivAt (fun i => (B i).size) T).toOpenPartialHomeomorph
      (realSchurMixedExpCoordinates (fun i => (B i).size) T)

theorem realSchurMixedLocalChart_zero_mem_source
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data) :
    0 ∈ (realSchurMixedLocalChart B T hT hdiag hsep).source :=
  (show HasStrictFDerivAt
      (realSchurMixedExpCoordinates (fun i => (B i).size) T)
      (realSchurMixedTangentEquiv B T hT hdiag hsep :
        RealSchurMixedTangent (fun i => (B i).size) →L[ℝ]
          Matrix (RealSchurMixedCoord (fun i => (B i).size))
            (RealSchurMixedCoord (fun i => (B i).size)) ℝ) 0 from
    realSchurMixedExpCoordinates_hasStrictFDerivAt (fun i => (B i).size) T).mem_toOpenPartialHomeomorph_source

theorem realSchurMixedLocalChart_center_mem_target
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data) :
    T ∈ (realSchurMixedLocalChart B T hT hdiag hsep).target := by
  have h := (realSchurMixedLocalChart B T hT hdiag hsep).map_source
    (realSchurMixedLocalChart_zero_mem_source B T hT hdiag hsep)
  change realSchurMixedExpCoordinates (fun i => (B i).size) T 0 ∈ _ at h
  rwa [realSchurMixedExpCoordinates_zero] at h

#print axioms realSchurMixedExpCoordinates_hasStrictFDerivAt
#print axioms realSchurMixedLocalChart
#print axioms realSchurMixedLocalChart_zero_mem_source
#print axioms realSchurMixedLocalChart_center_mem_target
end SpectralRadiusUpperTail
