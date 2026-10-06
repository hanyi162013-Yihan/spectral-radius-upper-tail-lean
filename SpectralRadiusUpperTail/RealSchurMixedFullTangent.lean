import SpectralRadiusUpperTail.RealSchurMixedAngularInverse
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator RightActions

/-- Matrix variations whose lower Schur blocks vanish. -/
noncomputable def realSchurMixedUpperSubmodule
    {m : ℕ} (s : Fin m → ℕ) :
    Submodule ℝ (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  (realSchurMixedLowerProjection s).ker

abbrev RealSchurMixedTangent {m : ℕ} (s : Fin m → ℕ) :=
  (RealSchurMixedOrbitIndex s → ℝ) × realSchurMixedUpperSubmodule s

/-- The complete first-order Schur map: a skew angular direction plus a
block-upper matrix variation. -/
noncomputable def realSchurMixedTangentMap
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    RealSchurMixedTangent s →ₗ[ℝ]
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ where
  toFun x := x.2.val +
    (realSchurMixedSkewEmbed s x.1*T - T*realSchurMixedSkewEmbed s x.1)
  map_add' x y := by
    change (x.2.val+y.2.val) +
      (realSchurMixedSkewEmbed s (x.1+y.1)*T -
        T*realSchurMixedSkewEmbed s (x.1+y.1)) = _
    rw [realSchurMixedSkewEmbed_add, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' a x := by
    change a • x.2.val +
      (realSchurMixedSkewEmbed s (a • x.1)*T -
        T*realSchurMixedSkewEmbed s (a • x.1)) = _
    rw [realSchurMixedSkewEmbed_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_sub]
    rfl

theorem realSchurMixedTangentMap_lower
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x : RealSchurMixedTangent s) :
    realSchurMixedLowerProjection s (realSchurMixedTangentMap s T x) =
      (realSchurMixedOrbitMatrix s T).mulVec x.1 := by
  have hD : realSchurMixedLowerProjection s x.2.val = 0 := x.2.property
  change realSchurMixedLowerProjection s
    (x.2.val + (realSchurMixedSkewEmbed s x.1*T -
      T*realSchurMixedSkewEmbed s x.1)) = _
  rw [map_add, hD, zero_add]
  funext p
  exact realSchurMixedSkewEmbed_lower_action s T x.1 p

/-- The full tangent map has no kernel when all diagonal block spectra are
separated. -/
theorem realSchurMixedTangentMap_injective
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data) :
    Function.Injective
      (realSchurMixedTangentMap (fun i => (B i).size) T) := by
  let s := fun i : Fin m => (B i).size
  let J := realSchurMixedAngularDerivativeEquiv B T hT hdiag hsep
  rintro ⟨ω,D⟩ ⟨η,E⟩ h
  have hl := congrArg (realSchurMixedLowerProjection s) h
  rw [realSchurMixedTangentMap_lower,
    realSchurMixedTangentMap_lower] at hl
  have hω : ω = η := J.injective (by
    rw [realSchurMixedAngularDerivativeEquiv_apply,
      realSchurMixedAngularDerivativeEquiv_apply]
    exact hl)
  apply Prod.ext hω
  apply Subtype.ext
  change D.val + (realSchurMixedSkewEmbed s ω*T -
    T*realSchurMixedSkewEmbed s ω) =
      E.val + (realSchurMixedSkewEmbed s η*T -
        T*realSchurMixedSkewEmbed s η) at h
  rw [hω] at h
  exact add_right_cancel h

/-- Every full matrix variation decomposes uniquely into an angular
commutator and a variation supported in the block-upper entries. -/
theorem realSchurMixedTangentMap_surjective
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data) :
    Function.Surjective
      (realSchurMixedTangentMap (fun i => (B i).size) T) := by
  let s := fun i : Fin m => (B i).size
  let J := realSchurMixedAngularDerivativeEquiv B T hT hdiag hsep
  intro A
  let ω : RealSchurMixedOrbitIndex s → ℝ :=
    J.symm (realSchurMixedLowerProjection s A)
  let C := realSchurMixedSkewEmbed s ω*T - T*realSchurMixedSkewEmbed s ω
  have hC : realSchurMixedLowerProjection s C =
      realSchurMixedLowerProjection s A := by
    calc
      realSchurMixedLowerProjection s C =
          (realSchurMixedOrbitMatrix s T).mulVec ω := by
        funext p
        exact realSchurMixedSkewEmbed_lower_action s T ω p
      _ = J ω := (realSchurMixedAngularDerivativeEquiv_apply
        B T hT hdiag hsep ω).symm
      _ = realSchurMixedLowerProjection s A := J.apply_symm_apply _
  have hD : A-C ∈ realSchurMixedUpperSubmodule s := by
    change realSchurMixedLowerProjection s (A-C) = 0
    rw [map_sub, hC, sub_self]
  refine ⟨(ω,⟨A-C,hD⟩), ?_⟩
  change A-C+C=A
  exact sub_add_cancel A C

/-- The complete mixed-block Schur tangent is a continuous linear
equivalence. -/
noncomputable def realSchurMixedTangentEquiv
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data) :
    RealSchurMixedTangent (fun i => (B i).size) ≃L[ℝ]
      Matrix (RealSchurMixedCoord (fun i => (B i).size))
        (RealSchurMixedCoord (fun i => (B i).size)) ℝ :=
  (LinearEquiv.ofBijective
    (realSchurMixedTangentMap (fun i => (B i).size) T)
    ⟨realSchurMixedTangentMap_injective B T hT hdiag hsep,
      realSchurMixedTangentMap_surjective B T hT hdiag hsep⟩).toContinuousLinearEquiv

#print axioms realSchurMixedTangentMap_injective
#print axioms realSchurMixedTangentMap_surjective
#print axioms realSchurMixedTangentEquiv
end SpectralRadiusUpperTail
