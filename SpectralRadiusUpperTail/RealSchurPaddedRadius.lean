import SpectralRadiusUpperTail.RealSchurPaddedRadiusTransfer
import SpectralRadiusUpperTail.RealSchurDiagonalSpectrum

namespace SpectralRadiusUpperTail

/-- The spectral radius of the complete padded Schur product-model matrix
is bounded by the largest radius of its diagonal eigenvalue data, for every
choice of Gaussian bridge and gap coordinates. -/
theorem realSchurPaddedMatrix_radius_le {N : ℕ}
    (n : ℕ) (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hmod : ∀ i, realSchurDataRadius (B i) ≤ ρ) :
    (spectralRadius ℂ ((flattenSchurBlocks
      (realSchurPaddedMatrix n B z)).map Complex.ofRealHom)).toReal ≤ ρ := by
  apply flattenSchurBlocks_upper_radius_le
    (realSchurPaddedMatrix n B z) (realSchurPaddedMatrix_upper n B z) ρ hρ
  intro i w hw
  have heq : realSchurPaddedMatrix n B z i i =
      realSchurDataPower (B i) 1 (z.1 i) := by
    simp [realSchurPaddedMatrix]
  rw [heq] at hw
  exact (realSchurDataPower_spectrum_norm_le (B i) (z.1 i) w hw).trans
    (hmod i)

/-- Each diagonal datum has an eigenvalue in the full padded matrix, so
its radius cannot exceed the full spectral radius. -/
theorem realSchurDataRadius_le_paddedMatrix_radius {N : ℕ}
    (n : ℕ) (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (i : Fin N) :
    realSchurDataRadius (B i) ≤
      (spectralRadius ℂ ((flattenSchurBlocks
        (realSchurPaddedMatrix n B z)).map Complex.ofRealHom)).toReal := by
  let A := realSchurPaddedMatrix n B z
  obtain ⟨w, hw, hnorm⟩ :=
    realSchurDataPower_radius_witness (B i) (z.1 i)
  have hdiag : A i i = realSchurDataPower (B i) 1 (z.1 i) := by
    simp [A, realSchurPaddedMatrix]
  have hblock : w ∈ spectrum ℂ ((A i i).map Complex.ofRealHom) := by
    rwa [hdiag]
  have hfull := flattenSchurBlocks_upper_spectrum_of_block A
    (realSchurPaddedMatrix_upper n B z) i w hblock
  rw [← hnorm]
  exact flattenSchurBlocks_eigenvalue_le_radius A w hfull

/-- The block-radius condition used in the Gaussian Schur moment calculation
is exactly the spectral-radius condition on the full padded matrix. -/
theorem realSchurPaddedMatrix_radius_le_iff {N : ℕ}
    (n : ℕ) (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (spectralRadius ℂ ((flattenSchurBlocks
      (realSchurPaddedMatrix n B z)).map Complex.ofRealHom)).toReal ≤ ρ ↔
      ∀ i, realSchurDataRadius (B i) ≤ ρ := by
  constructor
  · intro h i
    exact (realSchurDataRadius_le_paddedMatrix_radius n B z i).trans h
  · intro h
    exact realSchurPaddedMatrix_radius_le n B z ρ hρ h

#print axioms realSchurPaddedMatrix_radius_le
#print axioms realSchurDataRadius_le_paddedMatrix_radius
#print axioms realSchurPaddedMatrix_radius_le_iff
end SpectralRadiusUpperTail
