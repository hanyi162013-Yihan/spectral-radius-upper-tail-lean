import SpectralRadiusUpperTail.RealSchurGlobalBlockOrbitDiagonal
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Elementary real 2×2 bridge matrices in the coordinate convention used
by the pair–pair Sylvester operator. -/
def realSchurBridgeBasis (q : Fin 4) : Matrix (Fin 2) (Fin 2) ℝ :=
  if q = 0 then !![1, 0; 0, 0]
  else if q = 1 then !![0, 1; 0, 0]
  else if q = 2 then !![0, 0; 1, 0]
  else !![0, 0; 0, 1]

theorem realSchurBridgeBasis_vector (q : Fin 4) :
    realSchurBridgeVector (realSchurBridgeBasis q) = Pi.single q 1 := by
  funext i
  fin_cases q <;> fin_cases i <;>
    simp [realSchurBridgeBasis, realSchurBridgeVector, Pi.single, Fin.ext_iff]

theorem realSchurBridgeBasis_sylvester_column
    (A : Matrix (Fin 4) (Fin 4) ℝ) (q i : Fin 4) :
    (A.mulVec (realSchurBridgeVector (realSchurBridgeBasis q))) i = A i q := by
  rw [realSchurBridgeBasis_vector, Matrix.mulVec_single_one]
  rfl

#print axioms realSchurBridgeBasis_vector
#print axioms realSchurBridgeBasis_sylvester_column
end SpectralRadiusUpperTail
