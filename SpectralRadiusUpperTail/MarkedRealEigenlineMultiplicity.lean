import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- At a simple characteristic spectrum, fixing the real eigenvalue fixes
its eigenline. This is the algebraic part of the multiplicity-two count in
the marked-eigenline change of variables. -/
theorem real_eigenvectors_collinear_of_separable
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (hsep : f.charpoly.Separable)
    (x : ℝ) (v w : E) (hv : v ≠ 0)
    (hfv : f v = x • v) (hfw : f w = x • w) :
    ∃ c : ℝ, c • v = w := by
  have hvmem : v ∈ Module.End.eigenspace f x := Module.End.mem_eigenspace_iff.mpr hfv
  have hwmem : w ∈ Module.End.eigenspace f x := Module.End.mem_eigenspace_iff.mpr hfw
  have hspan : ℝ ∙ v ≤ Module.End.eigenspace f x :=
    (Submodule.span_singleton_le_iff_mem v _).mpr hvmem
  have hlower : 1 ≤ Module.finrank ℝ (Module.End.eigenspace f x) := by
    have hspanrank : Module.finrank ℝ (ℝ ∙ v) = 1 :=
      finrank_span_singleton hv
    rw [← hspanrank]
    exact Submodule.finrank_mono hspan
  have hupper : Module.finrank ℝ (Module.End.eigenspace f x) ≤ 1 :=
    (LinearMap.finrank_eigenspace_le f x).trans
      (Polynomial.rootMultiplicity_le_one_of_separable hsep x)
  have hdim : Module.finrank ℝ (Module.End.eigenspace f x) = 1 := by omega
  let v' : Module.End.eigenspace f x := ⟨v, hvmem⟩
  let w' : Module.End.eigenspace f x := ⟨w, hwmem⟩
  have hv' : v' ≠ 0 := by
    intro hzero
    apply hv
    exact congrArg Subtype.val hzero
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' v' hv').mp hdim w'
  refine ⟨c, ?_⟩
  exact congrArg Subtype.val hc

/-- For a simple real eigenvalue, the unit sphere marks its eigenline in
exactly two ways. -/
theorem real_unit_eigenvectors_eq_or_neg_of_separable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (hsep : f.charpoly.Separable)
    (x : ℝ) (v w : E)
    (hvnorm : ‖v‖ = 1) (hwnorm : ‖w‖ = 1)
    (hfv : f v = x • v) (hfw : f w = x • w) :
    w = v ∨ w = -v := by
  have hv : v ≠ 0 := by
    intro hzero
    simp [hzero] at hvnorm
  obtain ⟨c, hc⟩ :=
    real_eigenvectors_collinear_of_separable f hsep x v w hv hfv hfw
  have habs : |c| = 1 := by
    have h := congrArg (norm : E → ℝ) hc
    simpa only [norm_smul, Real.norm_eq_abs, hvnorm, hwnorm,
      mul_one] using h
  by_cases hcpos : 0 ≤ c
  · have hc1 : c = 1 := by simpa only [abs_of_nonneg hcpos] using habs
    left
    simpa [hc1] using hc.symm
  · have hc1 : c = -1 := by
      rw [abs_of_neg (lt_of_not_ge hcpos)] at habs
      linarith
    right
    simpa [hc1] using hc.symm

#print axioms real_eigenvectors_collinear_of_separable
#print axioms real_unit_eigenvectors_eq_or_neg_of_separable
end SpectralRadiusUpperTail
