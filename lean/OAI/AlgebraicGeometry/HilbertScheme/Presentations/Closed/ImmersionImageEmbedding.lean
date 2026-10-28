import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

/-! # Immersion Image Embedding -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionImageEmbedding

noncomputable section

/-! A closed embedding of a presentation of a closed subscheme transports
to its actual ideal-sheaf image, preserving kernels and all specified projections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {F A Q P : Scheme.{u}} (k : F ⟶ A) [IsClosedImmersion k] (e : Q ≅ F) (j : Q ⟶ P)

def closedImagePresentationIso : Q ≅ k.ker.subscheme := e ≪≫ asIso k.toImage

def closedImageEmbedding : k.ker.subscheme ⟶ P := (closedImagePresentationIso k e).inv ≫ j

instance closedImageEmbedding_isClosedImmersion [IsClosedImmersion j] :
    IsClosedImmersion (closedImageEmbedding k e j) :=
  inferInstanceAs (IsClosedImmersion ((closedImagePresentationIso k e).inv ≫ j))

theorem closedImageEmbedding_ker : (closedImageEmbedding k e j).ker = j.ker := by
  rw [closedImageEmbedding, Scheme.Hom.ker_comp_of_isIso]

theorem closedImagePresentationIso_inclusion :
    (closedImagePresentationIso k e).hom ≫ k.ker.subschemeι = e.hom ≫ k := by
  change (e.hom ≫ k.toImage) ≫ k.imageι = _
  rw [Category.assoc, Scheme.Hom.toImage_imageι]

theorem closedImageEmbedding_compatibility {B : Scheme.{u}} (r : A ⟶ B) (q : P ⟶ B)
    (h : e.hom ≫ k ≫ r = j ≫ q) : closedImageEmbedding k e j ≫ q = k.ker.subschemeι ≫ r := by
  apply (cancel_epi (closedImagePresentationIso k e).hom).mp
  have hl : (closedImagePresentationIso k e).hom ≫ closedImageEmbedding k e j = j := by
    exact Iso.hom_inv_id_assoc _ _
  calc
    _ = ((closedImagePresentationIso k e).hom ≫ closedImageEmbedding k e j) ≫ q :=
      (Category.assoc _ _ _).symm
    _ = j ≫ q := congrArg (fun l => l ≫ q) hl
    _ = e.hom ≫ k ≫ r := h.symm
    _ = ((closedImagePresentationIso k e).hom ≫ k.ker.subschemeι) ≫ r :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun l => l ≫ r) (closedImagePresentationIso_inclusion k e)).symm
    _ = _ := Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionImageEmbedding
