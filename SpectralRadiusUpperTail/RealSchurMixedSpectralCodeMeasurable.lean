import SpectralRadiusUpperTail.RealSchurMixedSpectralCode

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

theorem realSchurMixed_block_charpoly_at_label_measurable
    {m : ℕ} (s : Fin m → ℕ) (a : Fin m)
    (i : Fin (Fintype.card (RealSchurMixedCoord s))) :
    Measurable (fun T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ =>
      ((realSchurMixedDiagonalMatrix s T a).charpoly.map Complex.ofRealHom).eval
        (realSchurMixedCanonicalSpectrum s T i)) := by
  have hz : Measurable (fun T => realSchurMixedCanonicalSpectrum s T i) :=
    (measurable_pi_apply i).comp (realSchurMixedCanonicalSpectrum_measurable s)
  have hM : Continuous (fun z : ℂ ×
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ =>
      Matrix.scalar (Fin (s a)) z.1 -
        (realSchurMixedDiagonalMatrix s z.2 a).map Complex.ofRealHom) := by
    apply continuous_matrix
    intro j k
    change Continuous (fun z : ℂ ×
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ =>
        (if j=k then z.1 else 0) - (z.2 ⟨a,j⟩ ⟨a,k⟩ : ℂ))
    split_ifs <;> fun_prop
  have hdet := hM.matrix_det.measurable.comp (hz.prodMk measurable_id)
  simpa only [← Matrix.charpoly_map, Matrix.eval_charpoly, Function.comp_def, id_eq] using hdet

/-- The finite root-membership classification is Borel. Its fibers can
therefore be used directly as domains in the area formula. -/
theorem realSchurMixedSpectralCode_measurable
    {m : ℕ} (s : Fin m → ℕ) : Measurable (realSchurMixedSpectralCode s) := by
  classical
  apply measurable_pi_lambda
  intro a
  apply measurable_pi_lambda
  intro i
  apply measurable_to_bool
  have he : (fun T => realSchurMixedSpectralCode s T a i) ⁻¹' {true} =
      {T | ((realSchurMixedDiagonalMatrix s T a).charpoly.map Complex.ofRealHom).eval
        (realSchurMixedCanonicalSpectrum s T i)=0} := by
    ext T
    simp only [Set.mem_preimage, Set.mem_singleton_iff, realSchurMixedSpectralCode,
      decide_eq_true_eq, Set.mem_ofPred_eq]
  rw [he]
  exact measurableSet_eq_fun (realSchurMixed_block_charpoly_at_label_measurable s a i)
    measurable_const

#print axioms realSchurMixed_block_charpoly_at_label_measurable
#print axioms realSchurMixedSpectralCode_measurable
end SpectralRadiusUpperTail
