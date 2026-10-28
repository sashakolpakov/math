import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.FrameComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions

/-! # Product Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.ProductPullbacks

noncomputable section

/-! Canonical open-pullback comparisons for both ways of forming powers and tensor products. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem tensorPowerSection_postcomp {L M : X.Modules}
    (s : Line.Bundles.structureModule X ⟶ L) (a : L ⟶ M) (n : ℕ) :
    Maps.tensorPowerSection s n ≫ Maps.tensorPowerMap a n = Maps.tensorPowerSection (s ≫ a) n := by
  simp only [Maps.tensorPowerSection, Maps.tensorPowerMap_comp, Category.assoc]

variable (f : X ⟶ Y) [IsOpenImmersion f] (L M : Y.Modules) (n : ℕ)

def tensorPowerOfTensorPullbackIso :
    (Scheme.Modules.pullback f).obj (PowerSheaf.tensorPowerModule (Tensor.ProductSheaf.tensorModule L M) n) ≅
      PowerSheaf.tensorPowerModule (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj L)
        ((Scheme.Modules.pullback f).obj M)) n :=
  asIso (Power.PullbackComparison.powerPullbackComparison f (Tensor.ProductSheaf.tensorModule L M) n) ≪≫
    (Maps.tensorPowerFunctor X n).mapIso (asIso (Tensor.PullbackComparison.tensorPullbackComparison f L M))

def tensorOfPowersPullbackIso :
    (Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule (PowerSheaf.tensorPowerModule L n) (PowerSheaf.tensorPowerModule M n)) ≅
      Tensor.ProductSheaf.tensorModule (PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj L) n)
        (PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj M) n) :=
  asIso (Tensor.PullbackComparison.tensorPullbackComparison f (PowerSheaf.tensorPowerModule L n) (PowerSheaf.tensorPowerModule M n)) ≪≫
    Tensor.Bifunctor.tensorModuleMapIso (asIso (Power.PullbackComparison.powerPullbackComparison f L n)) (asIso (Power.PullbackComparison.powerPullbackComparison f M n))

theorem tensorPowerOfTensorPullbackIso_section
    (s : Line.Bundles.structureModule Y ⟶ L) (t : Line.Bundles.structureModule Y ⟶ M) :
    Ample.LineBundles.pullbackSection f (Maps.tensorPowerSection (Tensor.ProductSections.tensorProductSection s t) n) ≫
      (tensorPowerOfTensorPullbackIso f L M n).hom =
      Maps.tensorPowerSection (Tensor.ProductSections.tensorProductSection (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t)) n := by
  change _ ≫ (Power.PullbackComparison.powerPullbackComparison f (Tensor.ProductSheaf.tensorModule L M) n ≫
    Maps.tensorPowerMap (Tensor.PullbackComparison.tensorPullbackComparison f L M) n) = _
  rw [← Category.assoc, Power.SectionBaseChange.powerPullbackComparison_section, tensorPowerSection_postcomp,
    Tensor.SectionBaseChange.tensorPullbackComparison_section]

theorem tensorOfPowersPullbackIso_section
    (s : Line.Bundles.structureModule Y ⟶ L) (t : Line.Bundles.structureModule Y ⟶ M) :
    Ample.LineBundles.pullbackSection f (Tensor.ProductSections.tensorProductSection (Maps.tensorPowerSection s n) (Maps.tensorPowerSection t n)) ≫
      (tensorOfPowersPullbackIso f L M n).hom =
      Tensor.ProductSections.tensorProductSection (Maps.tensorPowerSection (Ample.LineBundles.pullbackSection f s) n)
        (Maps.tensorPowerSection (Ample.LineBundles.pullbackSection f t) n) := by
  change _ ≫ (Tensor.PullbackComparison.tensorPullbackComparison f (PowerSheaf.tensorPowerModule L n) (PowerSheaf.tensorPowerModule M n) ≫
    Tensor.Bifunctor.tensorModuleMap (Power.PullbackComparison.powerPullbackComparison f L n) (Power.PullbackComparison.powerPullbackComparison f M n)) = _
  rw [← Category.assoc, Tensor.SectionBaseChange.tensorPullbackComparison_section, Tensor.ProductSections.tensorProductSection_postcomp,
    Power.SectionBaseChange.powerPullbackComparison_section, Power.SectionBaseChange.powerPullbackComparison_section]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.ProductPullbacks
