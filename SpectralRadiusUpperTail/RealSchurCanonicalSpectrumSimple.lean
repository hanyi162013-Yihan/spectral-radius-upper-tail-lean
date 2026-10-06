import SpectralRadiusUpperTail.RealSchurMixedCanonicalSpectrum

namespace SpectralRadiusUpperTail

theorem realSchurMixedCanonicalSpectrum_isRoot
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : T.charpoly.Separable) (i : Fin (Fintype.card (RealSchurMixedCoord s))) :
    (T.charpoly.map Complex.ofRealHom).eval (realSchurMixedCanonicalSpectrum s T i)=0 := by
  apply (Polynomial.mem_roots (Polynomial.map_monic_ne_zero (Matrix.charpoly_monic T))).mp
  rw [realSchurMixedCanonicalSpectrum_roots s T hT]
  exact Multiset.mem_map.mpr ⟨i,by simp,rfl⟩

theorem realSchurMixedCanonicalSpectrum_injective
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : T.charpoly.Separable) :
    Function.Injective (realSchurMixedCanonicalSpectrum s T) := by
  have hn := Polynomial.nodup_roots ((Polynomial.separable_map (algebraMap ℝ ℂ)).mpr hT)
  change (T.charpoly.map Complex.ofRealHom).roots.Nodup at hn
  rw [realSchurMixedCanonicalSpectrum_roots s T hT] at hn
  have h := (Multiset.nodup_map_iff_inj_on (Finset.nodup _)).mp hn
  intro i j hij
  exact h i (by simp) j (by simp) hij

#print axioms realSchurMixedCanonicalSpectrum_isRoot
#print axioms realSchurMixedCanonicalSpectrum_injective
end SpectralRadiusUpperTail
