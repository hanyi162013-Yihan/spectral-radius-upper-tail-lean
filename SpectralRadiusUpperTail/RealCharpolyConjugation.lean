import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The characteristic polynomial of a real matrix takes conjugate values
at conjugate complex arguments. -/
theorem real_matrix_complex_charpoly_eval_conj
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (w : ℂ) :
    star (((M.map Complex.ofRealHom).charpoly).eval w) =
      ((M.map Complex.ofRealHom).charpoly).eval (star w) := by
  classical
  let C : Matrix ι ι ℂ := M.map Complex.ofRealHom
  have hC : C.map (starRingEnd ℂ) = C := by
    ext i j
    simp [C]
  have hchar : C.charpoly.map (starRingEnd ℂ) = C.charpoly := by
    rw [← Matrix.charpoly_map, hC]
  have heval := Polynomial.eval_map_apply (f := starRingEnd ℂ)
    (p := C.charpoly) w
  rw [hchar] at heval
  simpa [C] using heval.symm

#print axioms real_matrix_complex_charpoly_eval_conj
end SpectralRadiusUpperTail
