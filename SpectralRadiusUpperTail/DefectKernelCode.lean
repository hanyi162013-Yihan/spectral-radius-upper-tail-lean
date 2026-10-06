import SpectralRadiusUpperTail.OccurrenceKernelCode
import SpectralRadiusUpperTail.IndexedFullReconstruction

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

lemma DefectRouteCertificate.exists_kernel_code (c : DefectRouteCertificate s v) :
    ∃ C : OccurrenceKernelCode (2*r),
      C.family = c.occurrenceFamily ∧ C.decode s = Setoid.ker v ∧
      C.gluing.card ≤ 8*(r+1-Fintype.card V) ∧
      C.restoration.card ≤ 8*(r+1-Fintype.card V)+1 := by
  obtain ⟨E,hE,F,hF,hrec⟩ := c.indexed_full_reconstruction
  let C : OccurrenceKernelCode (2*r) :=
    ⟨c.occurrenceFamily,c.indexedMatching,E,F⟩
  refine ⟨C,rfl,?_,hE,hF⟩
  apply Setoid.ext
  intro a b
  exact hrec a b

#print axioms DefectRouteCertificate.exists_kernel_code
end SpectralRadiusUpperTail
