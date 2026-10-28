import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.AssociatorFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions

/-! # Triple Tensor Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TripleTensorPullbacks

noncomputable section

/-! Pullback comparisons for the two parenthesizations of a triple tensor product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}
variable (f : X ⟶ Y) [IsOpenImmersion f] (L M N : Y.Modules)

def leftTripleTensorPullbackIso :
    (Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule L M) N) ≅
      Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj L)
        ((Scheme.Modules.pullback f).obj M)) ((Scheme.Modules.pullback f).obj N) :=
  asIso (Tensor.PullbackComparison.tensorPullbackComparison f (Tensor.ProductSheaf.tensorModule L M) N) ≪≫
    Tensor.Bifunctor.tensorModuleMapIso (asIso (Tensor.PullbackComparison.tensorPullbackComparison f L M)) (Iso.refl _)

def rightTripleTensorPullbackIso :
    (Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule L (Tensor.ProductSheaf.tensorModule M N)) ≅
      Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj L)
        (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)) :=
  asIso (Tensor.PullbackComparison.tensorPullbackComparison f L (Tensor.ProductSheaf.tensorModule M N)) ≪≫
    Tensor.Bifunctor.tensorModuleMapIso (Iso.refl _) (asIso (Tensor.PullbackComparison.tensorPullbackComparison f M N))

theorem leftTripleTensorPullbackIso_section
    (s : Line.Bundles.structureModule Y ⟶ L) (t : Line.Bundles.structureModule Y ⟶ M) (r : Line.Bundles.structureModule Y ⟶ N) :
    Ample.LineBundles.pullbackSection f (Tensor.ProductSections.tensorProductSection (Tensor.ProductSections.tensorProductSection s t) r) ≫
      (leftTripleTensorPullbackIso f L M N).hom =
      Tensor.ProductSections.tensorProductSection (Tensor.ProductSections.tensorProductSection (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t))
        (Ample.LineBundles.pullbackSection f r) := by
  change _ ≫ (Tensor.PullbackComparison.tensorPullbackComparison f (Tensor.ProductSheaf.tensorModule L M) N ≫
    Tensor.Bifunctor.tensorModuleMap (Tensor.PullbackComparison.tensorPullbackComparison f L M) (𝟙 _)) = _
  rw [← Category.assoc, Tensor.SectionBaseChange.tensorPullbackComparison_section, Tensor.ProductSections.tensorProductSection_postcomp,
    Tensor.SectionBaseChange.tensorPullbackComparison_section, Category.comp_id]

theorem rightTripleTensorPullbackIso_section
    (s : Line.Bundles.structureModule Y ⟶ L) (t : Line.Bundles.structureModule Y ⟶ M) (r : Line.Bundles.structureModule Y ⟶ N) :
    Ample.LineBundles.pullbackSection f (Tensor.ProductSections.tensorProductSection s (Tensor.ProductSections.tensorProductSection t r)) ≫
      (rightTripleTensorPullbackIso f L M N).hom =
      Tensor.ProductSections.tensorProductSection (Ample.LineBundles.pullbackSection f s)
        (Tensor.ProductSections.tensorProductSection (Ample.LineBundles.pullbackSection f t) (Ample.LineBundles.pullbackSection f r)) := by
  change _ ≫ (Tensor.PullbackComparison.tensorPullbackComparison f L (Tensor.ProductSheaf.tensorModule M N) ≫
    Tensor.Bifunctor.tensorModuleMap (𝟙 _) (Tensor.PullbackComparison.tensorPullbackComparison f M N)) = _
  rw [← Category.assoc, Tensor.SectionBaseChange.tensorPullbackComparison_section, Tensor.ProductSections.tensorProductSection_postcomp,
    Tensor.SectionBaseChange.tensorPullbackComparison_section, Category.comp_id]

theorem tensorAssociatorFrameIso_pullback
    (e : Line.Bundles.structureModule Y ⟶ L) (t : Line.Bundles.structureModule Y ⟶ M) (r : Line.Bundles.structureModule Y ⟶ N)
    [IsIso e] [IsIso t] [IsIso r] :
    (Scheme.Modules.pullback f).map (Tensor.AssociatorFrames.tensorAssociatorFrameIso e t r).hom ≫
      (rightTripleTensorPullbackIso f L M N).hom =
      (leftTripleTensorPullbackIso f L M N).hom ≫
        (Tensor.AssociatorFrames.tensorAssociatorFrameIso (Ample.LineBundles.pullbackSection f e) (Ample.LineBundles.pullbackSection f t) (Ample.LineBundles.pullbackSection f r)).hom := by
  apply (cancel_epi (Ample.LineBundles.pullbackSection f (Tensor.ProductSections.tensorProductSection (Tensor.ProductSections.tensorProductSection e t) r))).mp
  rw [← Category.assoc, ← Power.SectionTransitions.pullbackSection_postcomp, Tensor.AssociatorFrames.tensorAssociatorFrameIso_frame,
    rightTripleTensorPullbackIso_section, ← Category.assoc, leftTripleTensorPullbackIso_section,
    Tensor.AssociatorFrames.tensorAssociatorFrameIso_frame]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TripleTensorPullbacks
