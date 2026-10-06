import SpectralRadiusUpperTail.IidSignedWalkIntegral
import SpectralRadiusUpperTail.MatrixMappedWalkSum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma signedTrace_eq_path_sum (L : List Bool) (x : ι × ι → 𝕂) :
    (L.map (signedMatrixFactor (Matrix.of (fun i j => x (i,j))))).prod.trace =
      ∑ i, ∑ v : Fin L.length → ι,
        matrixMappedWalkTerm (signedMatrixFactor (Matrix.of (fun i j => x (i,j))))
          L (fun j => (1 : Matrix ι ι 𝕂) j i) i v := by
  simpa only [mul_one] using matrixMapped_trace_walk_sum
    (signedMatrixFactor (Matrix.of (fun i j => x (i,j)))) L (1 : Matrix ι ι 𝕂)

lemma iidSignedTrace_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ) (L : List Bool) :
    Integrable (fun x : ι × ι → 𝕂 =>
      (L.map (signedMatrixFactor (Matrix.of (fun i j => x (i,j))))).prod.trace)
      (Measure.pi (fun _ : ι × ι => μ)) := by
  classical
  simp_rw [signedTrace_eq_path_sum]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun v _ => iidSignedWalk_integrable μ c hc hexp L _ i v))

lemma iidSignedTrace_integral (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ) (L : List Bool) :
    (∫ x : ι × ι → 𝕂,
      (L.map (signedMatrixFactor (Matrix.of (fun i j => x (i,j))))).prod.trace
      ∂Measure.pi (fun _ : ι × ι => μ)) =
    ∑ i, ∑ v : Fin L.length → ι,
      (∏ e : ι × ι, ∫ z : 𝕂,
        z^(entryMultiplicity (fun a => (signedWalkEdge L i v a,L.get a)) (e,false)) *
        (star z)^(entryMultiplicity (fun a => (signedWalkEdge L i v a,L.get a)) (e,true)) ∂μ) *
      (1 : Matrix ι ι 𝕂) ((Fin.cons i v : Fin (L.length+1) → ι) (Fin.last L.length)) i := by
  classical
  simp_rw [signedTrace_eq_path_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun v _ => iidSignedWalk_integrable μ c hc hexp L _ i v))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun v _ => iidSignedWalk_integrable μ c hc hexp L _ i v)]
  apply Finset.sum_congr rfl
  intro v _
  exact iidSignedWalk_integral μ L _ i v

#print axioms signedTrace_eq_path_sum
#print axioms iidSignedTrace_integrable
#print axioms iidSignedTrace_integral
end SpectralRadiusUpperTail
