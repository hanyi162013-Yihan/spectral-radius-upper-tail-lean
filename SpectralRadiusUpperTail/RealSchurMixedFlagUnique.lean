import SpectralRadiusUpperTail.RealSchurMixedFlagPatches

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

theorem realSchurMixed_rotatedFrame_orthogonal
    {m : ℕ} (s : Fin m → ℕ) (R : RealSchurMixedOrthogonalFrame s)
    (w : RealSchurMixedOrbitIndex s → ℝ) :
    (R.val*realSchurMixedAngularFrame s w)ᵀ*
      (R.val*realSchurMixedAngularFrame s w)=1 := by
  rw [Matrix.transpose_mul]
  calc
    _ = (realSchurMixedAngularFrame s w)ᵀ*(R.valᵀ*R.val)*
        realSchurMixedAngularFrame s w := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [R.property, Matrix.mul_one, realSchurMixedAngularFrame_orthogonal]

/-- On the selected angle patches, a simple Schur representation with
prescribed ordered block spectra has a unique patch, angle, and upper
matrix. No upper entry is restricted by the patch selection. -/
theorem realSchurMixedFlag_representation_unique
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s)
    (k l : ℕ) (u v : RealSchurMixedOrbitIndex s → ℝ)
    (hu : u ∈ realSchurMixedFlagAnglePatch s hs c hc R k)
    (hv : v ∈ realSchurMixedFlagAnglePatch s hs c hc R l)
    (T U : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : T.BlockTriangular (fun i : RealSchurMixedCoord s => i.1))
    (hU : U.BlockTriangular (fun i : RealSchurMixedCoord s => i.1))
    (hsep : T.charpoly.Separable)
    (hdiag : ∀ a : Fin m,
      (U.toSquareBlock (fun i : RealSchurMixedCoord s => i.1) a).charpoly =
        (T.toSquareBlock (fun i : RealSchurMixedCoord s => i.1) a).charpoly)
    (heq : ((R k).val*realSchurMixedAngularFrame s u)*T*
        ((R k).val*realSchurMixedAngularFrame s u)ᵀ =
      ((R l).val*realSchurMixedAngularFrame s v)*U*
        ((R l).val*realSchurMixedAngularFrame s v)ᵀ) :
    k=l ∧ u=v ∧ T=U := by
  have hmark := realSchurBlockMarker_eq_of_ordered_spectra
    (fun i : RealSchurMixedCoord s => i.1) c _
    ((R k).val*realSchurMixedAngularFrame s u)
    ((R l).val*realSchurMixedAngularFrame s v) T U
    (realSchurMixed_rotatedFrame_orthogonal s (R k) u)
    (realSchurMixed_rotatedFrame_orthogonal s (R l) v)
    hT hU rfl heq hsep hdiag
  have hm : (R k).val*realSchurMixedFlagMarker s c u*(R k).valᵀ =
      (R l).val*realSchurMixedFlagMarker s c v*(R l).valᵀ := by
    simpa only [realSchurBlockMarker, realSchurMixedFlagMarker,
      Matrix.transpose_mul, Matrix.mul_assoc] using hmark
  have hkl : k=l := by
    by_contra hne
    have hd := pairwise_realSchurMixedFlagMarkerPatch s hs c hc R hne
    have hvl : (R l).val*realSchurMixedFlagMarker s c v*(R l).valᵀ ∈
        realSchurMixedFlagMarkerPatch s hs c hc R l := hv.2
    rw [← hm] at hvl
    exact Set.disjoint_left.mp hd hu.2 hvl
  subst l
  have hlocal : realSchurMixedAngularFrame s u*T*(realSchurMixedAngularFrame s u)ᵀ =
      realSchurMixedAngularFrame s v*U*(realSchurMixedAngularFrame s v)ᵀ := by
    apply (realMatrixOrthogonalConjugationEquiv _ (R k).val (R k).property).injective
    change (R k).val*(realSchurMixedAngularFrame s u*T*
        (realSchurMixedAngularFrame s u)ᵀ)*(R k).valᵀ =
      (R k).val*(realSchurMixedAngularFrame s v*U*
        (realSchurMixedAngularFrame s v)ᵀ)*(R k).valᵀ
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using heq
  exact ⟨rfl, realSchurMixedFlag_full_injective_ordered s hs c hc u v hu.1 hv.1
    T U hT hU hsep hdiag hlocal⟩

#print axioms realSchurMixed_rotatedFrame_orthogonal
#print axioms realSchurMixedFlag_representation_unique
end SpectralRadiusUpperTail
