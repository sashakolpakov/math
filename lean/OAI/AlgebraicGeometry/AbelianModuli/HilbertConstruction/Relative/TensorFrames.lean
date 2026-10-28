import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.PowerFrames

/-! # Tensor Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.TensorFrames

noncomputable section

/-! Frames of pulled-back tensor products and their compatibility with composition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

def relativeTensorFrame (f : X ⟶ Y) (L M : Line.Bundles.LineBundle Y)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf)
    (d : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M.sheaf) :
    Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule L.sheaf M.sheaf) := by
  let : IsIso (Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf) :=
    LineBundle.TensorBaseChange.lineBundle_tensorPullbackComparison_isIso f L M
  exact asIso (Tensor.ProductSections.tensorProductSection e.hom d.hom) ≪≫
    (asIso (Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf)).symm

theorem relativeTensorFrame_spec (f : X ⟶ Y) (L M : Line.Bundles.LineBundle Y)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf)
    (d : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M.sheaf) :
    (relativeTensorFrame f L M e d).hom ≫ Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf =
      Tensor.ProductSections.tensorProductSection e.hom d.hom := by
  let : IsIso (Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf) :=
    LineBundle.TensorBaseChange.lineBundle_tensorPullbackComparison_isIso f L M
  change (Tensor.ProductSections.tensorProductSection e.hom d.hom ≫ inv (Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf)) ≫
    Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem relativeTensorFrame_comp (f : X ⟶ Y) (g : Y ⟶ Z) (L M : Line.Bundles.LineBundle Z)
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj L.sheaf)
    (d : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj M.sheaf) :
    Ample.LineBundles.pullbackSection f (relativeTensorFrame g L M e d).hom ≫
      (Scheme.Modules.pullbackComp f g).hom.app (Tensor.ProductSheaf.tensorModule L.sheaf M.sheaf) =
      (relativeTensorFrame (f ≫ g) L M (PowerFrames.compositeBundleFrame f g L e) (PowerFrames.compositeBundleFrame f g M d)).hom := by
  let : IsIso (Tensor.PullbackComparison.tensorPullbackComparison (f ≫ g) L.sheaf M.sheaf) :=
    LineBundle.TensorBaseChange.lineBundle_tensorPullbackComparison_isIso (f ≫ g) L M
  apply (cancel_mono (Tensor.PullbackComparison.tensorPullbackComparison (f ≫ g) L.sheaf M.sheaf)).mp
  rw [relativeTensorFrame_spec, Category.assoc, ← Tensor.PullbackComposition.tensorPullbackComparison_comp]
  rw [← Category.assoc, ← Power.SectionTransitions.pullbackSection_postcomp, relativeTensorFrame_spec,
    ← Category.assoc, Tensor.SectionBaseChange.tensorPullbackComparison_section, Tensor.ProductSections.tensorProductSection_postcomp]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.TensorFrames
