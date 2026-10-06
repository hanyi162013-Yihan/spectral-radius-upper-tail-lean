import SpectralRadiusUpperTail.IidSignedTraceIntegral
import SpectralRadiusUpperTail.OrientedAssignmentMoment
import Mathlib.Data.Fin.Tuple.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma signedTrace_integral_eq_assignments (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ) (L : List Bool) :
    (∫ x : ι × ι → 𝕂,
      (L.map (signedMatrixFactor (Matrix.of (fun i j => x (i,j))))).prod.trace
      ∂Measure.pi (fun _ : ι × ι => μ)) =
    ∑ v : Fin (L.length+1) → ι,
      orientedAssignmentMoment μ L.get v * (1 : Matrix ι ι 𝕂) (v (Fin.last L.length)) (v 0) := by
  classical
  simp_rw [signedTrace_eq_path_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun v _ => iidSignedWalk_integrable μ c hc hexp L _ i v))]
  have hterm (i : ι) (v : Fin L.length → ι) :
      (∫ x : ι × ι → 𝕂,
        matrixMappedWalkTerm (signedMatrixFactor (Matrix.of (fun i j => x (i,j))))
          L (fun j => (1 : Matrix ι ι 𝕂) j i) i v ∂Measure.pi (fun _ : ι × ι => μ)) =
      orientedAssignmentMoment μ L.get (Fin.cons i v) *
        (1 : Matrix ι ι 𝕂) ((Fin.cons i v : Fin (L.length+1) → ι) (Fin.last L.length)) i := by
    simp_rw [signedMappedWalkTerm_product]
    rw [integral_mul_const]
    rfl
  simp_rw [integral_finsetSum _ (fun v _ => iidSignedWalk_integrable μ c hc hexp L _ _ v),hterm]
  have hh := (Fin.consEquiv (fun _ : Fin (L.length+1) => ι)).sum_comp
      (fun v => orientedAssignmentMoment μ L.get v *
        (1 : Matrix ι ι 𝕂) (v (Fin.last L.length)) (v 0))
  rw [Fintype.sum_prod_type] at hh
  exact hh

#print axioms signedTrace_integral_eq_assignments
end SpectralRadiusUpperTail
