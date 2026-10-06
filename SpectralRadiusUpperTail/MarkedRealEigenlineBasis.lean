import SpectralRadiusUpperTail.MarkedRealTwoBlockOrbit
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

abbrev markedRealFirstCoordinate (m : ℕ) :
    RealSchurMixedCoord (markedRealTwoBlockSizes m) :=
  ⟨0, markedRealZeroCoordinate m⟩

theorem markedRealTwoBlock_card (m : ℕ) :
    Fintype.card (RealSchurMixedCoord (markedRealTwoBlockSizes m)) = m+1 := by
  simp [RealSchurMixedCoord, Fintype.card_sigma, Fin.sum_univ_two,
    markedRealTwoBlockSizes, Nat.add_comm]

/-- A unit real eigenvector can be the first vector of an orthonormal
basis with one-dimensional first block and `m`-dimensional complement. -/
theorem exists_markedRealEigenlineBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ)
    (hdim : Module.finrank ℝ E = m+1)
    (v : E) (hv : ‖v‖ = 1) :
    ∃ b : OrthonormalBasis (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ E,
      b (markedRealFirstCoordinate m) = v := by
  let s : Set (RealSchurMixedCoord (markedRealTwoBlockSizes m)) :=
    {markedRealFirstCoordinate m}
  have hs : Subsingleton s := by infer_instance
  have horth : Orthonormal ℝ
      (s.domRestrict (fun _ : RealSchurMixedCoord (markedRealTwoBlockSizes m) => v)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hv
  obtain ⟨b,hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (by rw [hdim, markedRealTwoBlock_card])
  exact ⟨b, hb _ (by simp [s])⟩

#print axioms markedRealTwoBlock_card
#print axioms exists_markedRealEigenlineBasis
end SpectralRadiusUpperTail
