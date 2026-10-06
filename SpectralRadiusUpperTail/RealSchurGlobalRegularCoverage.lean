import SpectralRadiusUpperTail.RealSchurGlobalMixedSimpleBlocks
import SpectralRadiusUpperTail.RealSchurMixedSimpleRegular
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

theorem realSchurListBlockSize_mem
    (s : List ℕ) (i : Fin s.length) :
    realSchurListBlockSize s i ∈ s := by
  induction s with
  | nil => exact i.elim0
  | cons k ks ih =>
      induction i using Fin.cases with
      | zero => simp [realSchurListBlockSize]
      | succ i =>
          simp only [realSchurListBlockSize, Fin.cases_succ]
          exact List.mem_cons_of_mem k (ih i)

/-- Every finite-dimensional real endomorphism with simple spectrum has
an orthonormal mixed 1×1/2×2 block-upper representation at which the
angular Schur Jacobian is nonsingular. This establishes deterministic
regular-chart coverage in adapted coordinates; it does not calculate
the Gaussian one-point intensity. -/
theorem realLinearMap_exists_regular_mixed_block_upper
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] E)
    (hsep : f.charpoly.Separable) :
    ∃ s : List ℕ,
      (∀ k ∈ s, k = 1 ∨ k = 2) ∧
      ∃ b : OrthonormalBasis
        (RealSchurMixedCoord (realSchurListBlockSize s)) ℝ E,
        let T := LinearMap.toMatrix b.toBasis b.toBasis f
        realSchurMixedLowerProjection (realSchurListBlockSize s) T = 0 ∧
        (realSchurMixedOrbitMatrix (realSchurListBlockSize s) T).det ≠ 0 := by
  obtain ⟨s, hs, b, hT, _⟩ :=
    realLinearMap_exists_mixed_simple_blocks f hsep
  refine ⟨s, hs, b, hT, ?_⟩
  let T := LinearMap.toMatrix b.toBasis b.toBasis f
  have hTsep : T.charpoly.Separable := by
    have hchar : T.charpoly = f.charpoly := f.charpoly_toMatrix b.toBasis
    rw [hchar]
    exact hsep
  exact realSchurMixed_simpleSpectrum_orbit_det_ne_zero
    (realSchurListBlockSize s)
    (fun i => hs (realSchurListBlockSize s i)
      (realSchurListBlockSize_mem s i))
    T hT hTsep

#print axioms realLinearMap_exists_regular_mixed_block_upper
end SpectralRadiusUpperTail
