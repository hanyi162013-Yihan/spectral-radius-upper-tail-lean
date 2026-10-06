import SpectralRadiusUpperTail.RealSchurMixedEntrySplit
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

theorem realSchurMixedLowerEmbed_add
    {m : ℕ} (s : Fin m → ℕ)
    (ω η : RealSchurMixedOrbitIndex s → ℝ) :
    realSchurMixedLowerEmbed s (ω+η) =
      realSchurMixedLowerEmbed s ω + realSchurMixedLowerEmbed s η := by
  simp only [realSchurMixedLowerEmbed, Pi.add_apply, add_smul,
    Finset.sum_add_distrib]

theorem realSchurMixedLowerEmbed_smul
    {m : ℕ} (s : Fin m → ℕ) (a : ℝ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    realSchurMixedLowerEmbed s (a • ω) =
      a • realSchurMixedLowerEmbed s ω := by
  simp only [realSchurMixedLowerEmbed, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact mul_smul a (ω q) _

def realSchurMixedLowerEntryMap
    {m : ℕ} (s : Fin m → ℕ) :
    (RealSchurMixedOrbitIndex s → ℝ) →ₗ[ℝ]
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ where
  toFun := realSchurMixedLowerEmbed s
  map_add' := realSchurMixedLowerEmbed_add s
  map_smul' := realSchurMixedLowerEmbed_smul s

/-- Removing the exact lower entries leaves a matrix in the block-upper
submodule. -/
theorem realSchurMixed_upper_residual
    {m : ℕ} (s : Fin m → ℕ)
    (A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    A-realSchurMixedLowerEmbed s (realSchurMixedLowerProjection s A) ∈
      realSchurMixedUpperSubmodule s := by
  change realSchurMixedLowerProjection s
    (A-realSchurMixedLowerEmbed s (realSchurMixedLowerProjection s A)) = 0
  rw [map_sub, realSchurMixedLowerProjection_embed, sub_self]

/-- The complementary projection onto all block-upper entries. -/
noncomputable def realSchurMixedUpperEntries
    {m : ℕ} (s : Fin m → ℕ) :
    Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ →ₗ[ℝ]
      realSchurMixedUpperSubmodule s :=
  LinearMap.codRestrict (realSchurMixedUpperSubmodule s)
    (LinearMap.id - (realSchurMixedLowerEntryMap s).comp
      (realSchurMixedLowerProjection s).toLinearMap)
    (realSchurMixed_upper_residual s)

theorem realSchurMixedUpperEntries_upper
    {m : ℕ} (s : Fin m → ℕ)
    (D : realSchurMixedUpperSubmodule s) :
    realSchurMixedUpperEntries s D.val = D := by
  apply Subtype.ext
  change D.val - realSchurMixedLowerEmbed s
    (realSchurMixedLowerProjection s D.val) = D.val
  have hD : realSchurMixedLowerProjection s D.val = 0 := D.property
  rw [hD]
  have hz : realSchurMixedLowerEmbed s
      (0 : RealSchurMixedOrbitIndex s → ℝ) = 0 :=
    (realSchurMixedLowerEntryMap s).map_zero
  rw [hz, sub_zero]

/-- A fixed real-linear coordinate identification between all matrix
entries and the lower/angular plus block-upper variables. -/
noncomputable def realSchurMixedEntryEquiv
    {m : ℕ} (s : Fin m → ℕ) :
    Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ ≃ₗ[ℝ]
      RealSchurMixedTangent s where
  toFun A := (realSchurMixedLowerProjection s A,
    realSchurMixedUpperEntries s A)
  invFun x := realSchurMixedLowerEmbed s x.1 + x.2.val
  left_inv A := by
    change realSchurMixedLowerEmbed s (realSchurMixedLowerProjection s A) +
      (A-realSchurMixedLowerEmbed s (realSchurMixedLowerProjection s A)) = A
    abel
  right_inv x := by
    have hl : realSchurMixedLowerProjection s
        (realSchurMixedLowerEmbed s x.1+x.2.val) = x.1 := by
      have hD : realSchurMixedLowerProjection s x.2.val = 0 := x.2.property
      rw [map_add, realSchurMixedLowerProjection_embed, hD, add_zero]
    apply Prod.ext hl
    apply Subtype.ext
    change (realSchurMixedLowerEmbed s x.1+x.2.val) -
      realSchurMixedLowerEmbed s
        (realSchurMixedLowerProjection s
          (realSchurMixedLowerEmbed s x.1+x.2.val)) = x.2.val
    rw [hl]
    abel
  map_add' A C := by
    exact Prod.ext ((realSchurMixedLowerProjection s).map_add A C)
      ((realSchurMixedUpperEntries s).map_add A C)
  map_smul' a A := by
    exact Prod.ext ((realSchurMixedLowerProjection s).map_smul a A)
      ((realSchurMixedUpperEntries s).map_smul a A)

#print axioms realSchurMixedEntryEquiv
end SpectralRadiusUpperTail
