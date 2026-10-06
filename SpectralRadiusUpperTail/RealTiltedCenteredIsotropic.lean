import SpectralRadiusUpperTail.RealGaussianComparatorPerturbedIsotropic
import SpectralRadiusUpperTail.RealRankOneMap
import SpectralRadiusUpperTail.RealMatrixComplexNorm
import SpectralRadiusUpperTail.RealDescendingHSBudget
import SpectralRadiusUpperTail.RankOneTargetBound
import SpectralRadiusUpperTail.SequentialMatrixApproximation

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix

lemma real_tilted_centered_isotropic_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (4*c*‖x‖^2)) μ)
    (η L : ℝ) (hη : 0 < η) (hL : 0 ≤ L)
    (v : ℕ → ℕ → ℝ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hunit : ∀ n, 0 < n → (∑ j : Fin n, ‖v n j.val‖^2) = 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (b : ℝ) (r R ε : ℝ) (hr : 1 < r) (hR : 0 < R) (hε : 0 < ε) :
    Tendsto (fun n => (gaussianSequentialMatrixLaw μ (v n) (2*η) (rankOneTiltTarget η b (v n))).real
      {x | ¬ matrixAnnulusIsotropicControl
        ((normalizedArray (fun i => coordinateVector Prod.fst n (x i))-
          b • Matrix.vecMulVec (fun i : Fin n => v n i.val) (fun i : Fin n => v n i.val)).map Complex.ofRealHom)
        (fun i => (v n i.val : ℂ)) (fun i => (v n i.val : ℂ)) r R ε}) atTop (𝓝 0) := by
  let p := fun n (i : Fin n) => (v n i.val : ℂ)
  let t : (n : ℕ) → Fin n → ℝ := fun n => rankOneTiltTarget η b (v n)
  let D := fun n => (descendingTriangularInverse η (fun i : Fin n => v n i.val)).map Complex.ofRealHom-1
  let Er := fun n (x : Fin n → Fin n → ℝ × ℝ) =>
    normalizedArray (fun i => coordinateVector Prod.fst n (x i)) -
      (normalizedArray (fun i => comparatorVector n (x i))*
        descendingTriangularInverse η (fun i : Fin n => v n i.val)+gaussianMeanMatrix (v n) (t n) η)
  let E := fun n x => (Er n x).map Complex.ofRealHom
  have herrReal := real_sequential_matrix_approximation μ hm hvar c hc hexp
    η ((η+1)*‖b‖*L) L hη hL v hv hunit hflat t
    (fun n i => rankOneTiltTarget_bound η hη b (v n) L (hflat n) i)
  have (n : ℕ) : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ (v n) (2*η) (t n)) :=
    gaussianSequentialMatrixLaw_probability μ (v n) (2*η) (by positivity) (t n)
  have herr : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      (gaussianSequentialMatrixLaw μ (v n) (2*η) (t n)).real
      {x | δ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (E n x)‖}) atTop (𝓝 0) := by
    intro δ hδ
    apply squeeze_zero (fun _ => measureReal_nonneg) _ (herrReal δ hδ)
    intro n
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    exact hx.trans (real_matrix_complex_opNorm_le (Er n x))
  have hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1 := by
    intro n
    simpa only [p,Complex.norm_real] using hv n
  have hpunit : ∀ n, 0 < n → (∑ i, ‖p n i‖^2) = 1 := by
    intro n hn
    simpa only [p,Complex.norm_real] using hunit n hn
  have ht := real_gaussianComparator_perturbed_isotropic_probability μ (4*c) (by positivity)
    hexp hm hvar v (fun _ => 2*η) (fun _ => by positivity) t D
    (1+Real.sqrt (1/(2*η^2))) (by positivity)
    (real_descendingTriangular_HS_budget η hη (fun n (i : Fin n) => v n i.val) hunit)
    p hp E herr r R ε hr hR hε
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ ht
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  letI := gaussianSequentialMatrixLaw_probability μ (v n) (2*η) (by positivity) (rankOneTiltTarget (n := n) η b (v n))
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx hz
  apply hx
  have he : (normalizedArray (fun i => comparatorVector n (x i))).map Complex.ofRealHom*(1+D n)+E n x =
      (normalizedArray (fun i => coordinateVector Prod.fst n (x i))-
        b • Matrix.vecMulVec (fun i : Fin n => v n i.val) (fun i : Fin n => v n i.val)).map Complex.ofRealHom := by
    dsimp only [D,E,Er]
    simp only [Matrix.map_sub _ (map_sub _),Matrix.map_add _ (map_add _),Matrix.map_mul]
    rw [real_gaussianMeanMatrix_rankOne η hη b (v n) (by omega) (hunit n (by omega)),real_rankOne_map]
    abel
  rwa [he] at hz

#print axioms real_tilted_centered_isotropic_probability
end SpectralRadiusUpperTail
