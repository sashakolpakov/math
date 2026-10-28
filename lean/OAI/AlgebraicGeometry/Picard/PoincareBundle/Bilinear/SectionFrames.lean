import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.UnitSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionFrames

/-! # Section Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.SectionFrames

noncomputable section

/-! An invertible product of two line sections makes both sections actual frames on an arbitrary scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionFrames

/-- A perfect bilinear line product and an invertible product section force both factor sections to be frames. -/
theorem isIso_of_product {X : Scheme.{u}} (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) {N : X.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L.sheaf M.sheaf N) [IsIso (BilinearPullback.toHom β)]
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M.sheaf)
    (v : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N) [IsIso v]
    (h : ∀ U : X.Opens, β.app U (s.app U (1 : Γ(X, U))) (t.app U (1 : Γ(X, U))) =
      v.app U (1 : Γ(X, U))) : IsIso s ∧ IsIso t := by
  have hp := UnitSections.product_eq β s t v h
  have : IsIso (AbelianModuli.HilbertConstruction.Tensor.ProductSections.tensorProductSection s t ≫ BilinearPullback.toHom β) := hp.symm ▸ inferInstance
  have : IsIso (AbelianModuli.HilbertConstruction.Tensor.ProductSections.tensorProductSection s t) :=
    (isIso_comp_right_iff (AbelianModuli.HilbertConstruction.Tensor.ProductSections.tensorProductSection s t) (BilinearPullback.toHom β)).mp inferInstance
  exact (AbelianModuli.HilbertConstruction.Tensor.SectionFrames.tensorProductSection_isIso_iff L M s t).mp inferInstance

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.SectionFrames
