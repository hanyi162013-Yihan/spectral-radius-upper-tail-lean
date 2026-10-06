import SpectralRadiusUpperTail.MatrixMappedWalkProduct
import SpectralRadiusUpperTail.MatrixSignedWord

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂]

def signedWalkEdge (L : List Bool) (i : ι) (v : Fin L.length → ι)
    (a : Fin L.length) : ι × ι :=
  if L.get a then ((Fin.cons i v : Fin (L.length+1) → ι) a.succ, (Fin.cons i v : Fin (L.length+1) → ι) a.castSucc)
  else ((Fin.cons i v : Fin (L.length+1) → ι) a.castSucc, (Fin.cons i v : Fin (L.length+1) → ι) a.succ)

lemma signedMappedWalkTerm_product (L : List Bool) (q : ι → 𝕂)
    (i : ι) (v : Fin L.length → ι) (x : ι × ι → 𝕂) :
    matrixMappedWalkTerm (signedMatrixFactor (Matrix.of (fun i j => x (i,j)))) L q i v =
      (∏ a : Fin L.length, if L.get a then star (x (signedWalkEdge L i v a))
        else x (signedWalkEdge L i v a)) * q ((Fin.cons i v : Fin (L.length+1) → ι) (Fin.last L.length)) := by
  rw [matrixMappedWalkTerm_product]
  simp only [signedMatrixFactor_oriented_entry, signedWalkEdge]

lemma iidSignedWalk_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (L : List Bool) (q : ι → 𝕂) (i : ι) (v : Fin L.length → ι) :
    Integrable (fun x : ι × ι → 𝕂 =>
      matrixMappedWalkTerm (signedMatrixFactor (Matrix.of (fun i j => x (i,j)))) L q i v)
      (Measure.pi (fun _ : ι × ι => μ)) := by
  simp_rw [signedMappedWalkTerm_product]
  exact (iidSignedWord_integrable μ c hc hexp (signedWalkEdge L i v) L.get).mul_const _

lemma iidSignedWalk_integral (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (L : List Bool) (q : ι → 𝕂) (i : ι) (v : Fin L.length → ι) :
    (∫ x : ι × ι → 𝕂,
      matrixMappedWalkTerm (signedMatrixFactor (Matrix.of (fun i j => x (i,j)))) L q i v
      ∂Measure.pi (fun _ : ι × ι => μ)) =
    (∏ e : ι × ι, ∫ z : 𝕂,
      z^(entryMultiplicity (fun a => (signedWalkEdge L i v a, L.get a)) (e,false)) *
      (star z)^(entryMultiplicity (fun a => (signedWalkEdge L i v a, L.get a)) (e,true)) ∂μ) *
      q ((Fin.cons i v : Fin (L.length+1) → ι) (Fin.last L.length)) := by
  simp_rw [signedMappedWalkTerm_product]
  rw [integral_mul_const, iidSignedWord_expectation]

#print axioms signedWalkEdge
#print axioms signedMappedWalkTerm_product
#print axioms iidSignedWalk_integrable
#print axioms iidSignedWalk_integral
end SpectralRadiusUpperTail
