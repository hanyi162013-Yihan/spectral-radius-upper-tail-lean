import SpectralRadiusUpperTail.RealSchurMixedOrbitDeterminant
import SpectralRadiusUpperTail.RealSchurMixedUpperAlgebra

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

noncomputable def realSchurMixedBlockScalar
    {m : ℕ} (s : Fin m → ℕ) (c : Fin m → ℝ) :
    Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
  Matrix.diagonal (fun i => c i.1)

theorem realSchurMixedBlockScalar_lower_zero
    {m : ℕ} (s : Fin m → ℕ) (c : Fin m → ℝ) :
    realSchurMixedLowerProjection s (realSchurMixedBlockScalar s c) = 0 := by
  funext p
  change (Matrix.diagonal (fun i : RealSchurMixedCoord s => c i.1))
    ⟨p.1.1.1,p.2.1⟩ ⟨p.1.1.2,p.2.2⟩ = 0
  apply Matrix.diagonal_apply_ne
  intro h
  exact (ne_of_gt p.1.2) (congrArg Sigma.fst h)

theorem realSchurMixedBlockScalar_sylvester
    {m : ℕ} (s : Fin m → ℕ) (c : Fin m → ℝ)
    (p : RealSchurLowerIndex m) :
    realSchurMixedSylvester s (realSchurMixedBlockScalar s c) p =
      Matrix.diagonal (fun _ : RealSchurMixedBridge s p => c p.1.1-c p.1.2) := by
  ext r z
  rcases r with ⟨i,j⟩
  rcases z with ⟨k,l⟩
  by_cases hi : i=k <;> by_cases hj : j=l <;>
    simp [realSchurMixedSylvester, realSchurMixedBlockScalar,
      hi, hj, eq_comm]

/-- Distinct scalar labels on the blocks give a regular Schur center,
even though a label may be repeated inside a block. -/
theorem realSchurMixedBlockScalar_orbit_det_ne_zero
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c) :
    (realSchurMixedOrbitMatrix s (realSchurMixedBlockScalar s c)).det ≠ 0 := by
  have hupper := (realSchurMixed_blockTriangular_iff_lower_zero s
    (realSchurMixedBlockScalar s c)).mpr (realSchurMixedBlockScalar_lower_zero s c)
  rw [realSchurMixedOrbitMatrix_det s hs _ (fun a b h i j => hupper h)]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  rw [realSchurMixedBlockScalar_sylvester, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  exact sub_ne_zero.mpr (fun h => (ne_of_gt p.2) (hc h))

#print axioms realSchurMixedBlockScalar_lower_zero
#print axioms realSchurMixedBlockScalar_sylvester
#print axioms realSchurMixedBlockScalar_orbit_det_ne_zero
end SpectralRadiusUpperTail
