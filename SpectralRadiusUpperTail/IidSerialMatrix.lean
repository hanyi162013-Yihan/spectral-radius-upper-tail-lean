import SpectralRadiusUpperTail.IidMatrixFlatten
import SpectralRadiusUpperTail.ActualMatrixIdentity
import SpectralRadiusUpperTail.EuclideanEntryMatrix

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable def serialMatrixEntries {n : ℕ} (x : Fin n → Fin n → ℂ) : Fin (n*n) → ℂ :=
  fun k => x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

lemma serialMatrixEntries_measurable (n : ℕ) :
    Measurable (serialMatrixEntries (n := n)) := by unfold serialMatrixEntries; fun_prop

lemma iid_serial_matrix_law (μ : Measure ℂ) [IsProbabilityMeasure μ] (n : ℕ) :
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).map serialMatrixEntries =
      Measure.pi (fun _ : Fin (n*n) => μ) := by
  have he := (measurePreserving_piCongrLeft (α := fun _ : Fin (n*n) => ℂ)
    (fun _ : Fin (n*n) => μ) finProdFinEquiv).map_eq
  rw [← iid_matrix_flatten_law μ n] at he
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at he
  convert! he using 1
  congr 1
  funext x k
  have hv := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin (n*n) => ℂ) finProdFinEquiv
    (fun ij : Fin n × Fin n => x ij.1 ij.2) (finProdFinEquiv.symm k)
  simpa only [Equiv.apply_symm_apply, Function.comp_apply, serialMatrixEntries] using hv.symm

lemma euclideanEntryMatrix_serial {n : ℕ} (x : Fin n → Fin n → ℂ) :
    euclideanEntryMatrix n (WithLp.toLp 2 (serialMatrixEntries x)) = Matrix.of x := by
  ext i j
  change x (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 = x i j
  rw [Equiv.symm_apply_apply]

lemma euclideanResidualMatrix_serial {n : ℕ} (x : Fin n → Fin n → ℂ) (z : ℂ) :
    euclideanResidualMatrix n z (WithLp.toLp 2 (serialMatrixEntries x)) = normalizedArray x-z • 1 := by
  rw [euclideanResidualMatrix, euclideanEntryMatrix_serial]
  congr 1

#print axioms serialMatrixEntries_measurable
#print axioms iid_serial_matrix_law
#print axioms euclideanEntryMatrix_serial
#print axioms euclideanResidualMatrix_serial
end SpectralRadiusUpperTail
