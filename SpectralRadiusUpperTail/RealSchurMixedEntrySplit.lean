import SpectralRadiusUpperTail.RealSchurMixedLocalShape
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- A lower-block matrix entry as a pair of global coordinates. -/
abbrev RealSchurMixedLowerEntry {m : ℕ} (s : Fin m → ℕ) :=
  {z : RealSchurMixedCoord s × RealSchurMixedCoord s // z.2.1 < z.1.1}

/-- The dependent lower-block index is exactly the corresponding subset
of ordinary matrix-entry indices. -/
def realSchurMixedLowerEntryEquiv {m : ℕ} (s : Fin m → ℕ) :
    RealSchurMixedOrbitIndex s ≃ RealSchurMixedLowerEntry s where
  toFun p := ⟨(⟨p.1.1.1,p.2.1⟩,⟨p.1.1.2,p.2.2⟩),p.1.2⟩
  invFun z := ⟨⟨(z.1.1.1,z.1.2.1),z.2⟩,(z.1.1.2,z.1.2.2)⟩
  left_inv p := by
    rcases p with ⟨⟨⟨i,j⟩,h⟩,⟨a,b⟩⟩
    rfl
  right_inv z := by
    rcases z with ⟨⟨⟨i,a⟩,⟨j,b⟩⟩,h⟩
    rfl

def realSchurMixedLowerRow {m : ℕ} (s : Fin m → ℕ)
    (p : RealSchurMixedOrbitIndex s) : RealSchurMixedCoord s :=
  ⟨p.1.1.1,p.2.1⟩

def realSchurMixedLowerCol {m : ℕ} (s : Fin m → ℕ)
    (p : RealSchurMixedOrbitIndex s) : RealSchurMixedCoord s :=
  ⟨p.1.1.2,p.2.2⟩

theorem realSchurMixedLowerEntry_injective {m : ℕ} (s : Fin m → ℕ) :
    Function.Injective (fun p : RealSchurMixedOrbitIndex s =>
      (realSchurMixedLowerRow s p, realSchurMixedLowerCol s p)) := by
  intro p q h
  apply (realSchurMixedLowerEntryEquiv s).injective
  apply Subtype.ext
  exact h

/-- Embed lower-block coordinates into a full matrix, with all other
entries zero. -/
def realSchurMixedLowerEmbed {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
  ∑ q, ω q • Matrix.single
    (realSchurMixedLowerRow s q) (realSchurMixedLowerCol s q) 1

theorem realSchurMixedLowerProjection_embed
    {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    realSchurMixedLowerProjection s (realSchurMixedLowerEmbed s ω) = ω := by
  classical
  funext p
  change (realSchurMixedLowerEmbed s ω)
    (realSchurMixedLowerRow s p) (realSchurMixedLowerCol s p) = ω p
  simp only [realSchurMixedLowerEmbed, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · simp [realSchurMixedLowerRow, realSchurMixedLowerCol]
  · intro q _ hqp
    have hne : ¬ (realSchurMixedLowerRow s q = realSchurMixedLowerRow s p ∧
        realSchurMixedLowerCol s q = realSchurMixedLowerCol s p) := by
      rintro ⟨hr,hc⟩
      exact hqp (realSchurMixedLowerEntry_injective s (Prod.ext hr hc))
    rw [Matrix.single_apply_of_ne _ _ _ _ _ hne, mul_zero]
  · simp

#print axioms realSchurMixedLowerEntry_injective
#print axioms realSchurMixedLowerProjection_embed
end SpectralRadiusUpperTail
