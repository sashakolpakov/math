import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenericBundleMapSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorBaseChange
import Mathlib.RingTheory.Noetherian.Basic

/-! # Section Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionMultiplication

noncomputable section

/-! Multiplication by a line-bundle section invertible on a nonempty open embeds sections of the other factor into sections of their tensor product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

def lineBundleSectionMultiply (L M : Line.Bundles.LineBundle X) (s : Line.Bundles.structureModule X ⟶ L.sheaf) :
    M.sheaf ⟶ (L.tensor M).sheaf :=
  (Tensor.ProductSheaf.tensorModuleUnitLeftIso M.sheaf).inv ≫ Tensor.Bifunctor.tensorModuleMap s (𝟙 M.sheaf)

theorem lineBundleSectionMultiply_pullback_isIso (f : Y ⟶ X)
    (L M : Line.Bundles.LineBundle X) (s : Line.Bundles.structureModule X ⟶ L.sheaf) [IsIso (Ample.LineBundles.pullbackSection f s)] :
    IsIso ((Scheme.Modules.pullback f).map (lineBundleSectionMultiply L M s)) := by
  have : IsIso ((Scheme.Modules.pullback f).map s) := (Section.Nonvanishing.isIso_pullbackSection_iff f s).mp inferInstance
  have := TensorBaseChange.lineBundle_tensorPullbackComparison_isIso f L M
  have : IsIso (Tensor.PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule X) M.sheaf) :=
    TensorBaseChange.lineBundle_tensorPullbackComparison_isIso f (Line.Bundles.LineBundle.trivial X) M
  have h : IsIso ((Scheme.Modules.pullback f).map (Tensor.Bifunctor.tensorModuleMap s (𝟙 M.sheaf)) ≫
      Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf) := by
    rw [Tensor.PullbackComparison.tensorPullbackComparison_natural]
    infer_instance
  have : IsIso ((Scheme.Modules.pullback f).map (Tensor.Bifunctor.tensorModuleMap s (𝟙 M.sheaf))) :=
    (isIso_comp_right_iff _ _).mp h
  exact (congrArg IsIso ((Scheme.Modules.pullback f).map_comp
    (Tensor.ProductSheaf.tensorModuleUnitLeftIso M.sheaf).inv (Tensor.Bifunctor.tensorModuleMap s (𝟙 M.sheaf)))).mpr inferInstance

theorem lineBundleSectionMultiply_sections_injective [IsIntegral X]
    {R : Type u} [CommRing R] (p : X ⟶ Spec (.of R))
    (L M : Line.Bundles.LineBundle X) (s : Line.Bundles.structureModule X ⟶ L.sheaf)
    [Nonempty (Ample.LineBundles.sectionNonvanishing s)] :
    Function.Injective ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).map (lineBundleSectionMultiply L M s)) := by
  have := lineBundleSectionMultiply_pullback_isIso (Ample.LineBundles.sectionNonvanishing s).ι L M s
  exact M.mapCoefficientSections_injective (L.tensor M) p (lineBundleSectionMultiply L M s)
    (Ample.LineBundles.sectionNonvanishing s)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionMultiplication
