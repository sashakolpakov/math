import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ImmersionFactorization

/-! # Embedding Kernel Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.EmbeddingKernelIso

noncomputable section

/-! Equal embedded ideal sheaves determine an actual isomorphism over the base, compatible with the embeddings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X Y P : Over S} (i : X ⟶ P) (j : Y ⟶ P)
variable [IsClosedImmersion i.left] [IsClosedImmersion j.left] (h : i.left.ker = j.left.ker)

def closedEmbeddingKernelIso : X ≅ Y := by
  let l : X.left ⟶ Y.left := IsClosedImmersion.lift j.left i.left h.symm.le
  have : IsIso l := IsClosedImmersion.isIso_lift j.left i.left h.symm
  exact Over.isoMk (asIso l) (by
    change l ≫ Y.hom = X.hom
    rw [← j.w, ← Category.assoc, IsClosedImmersion.lift_fac]
    exact i.w)

theorem closedEmbeddingKernelIso_embedding : (closedEmbeddingKernelIso i j h).hom ≫ j = i := by
  apply Over.OverMorphism.ext
  exact IsClosedImmersion.lift_fac j.left i.left h.symm.le

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.EmbeddingKernelIso
