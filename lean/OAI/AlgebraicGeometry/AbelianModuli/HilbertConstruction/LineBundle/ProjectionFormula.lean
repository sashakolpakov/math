import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorPullbackFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EquivalenceRightAdjointCommutation

/-! # Projection Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ProjectionFormula

noncomputable section

/-! The line-bundle projection formula is constructed from the actual pullback/direct-image adjunction and the proved tensor pullback natural isomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

def lineBundleProjectionFormulaIso (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y) (M : X.Modules) :
    Tensor.ProductSheaf.tensorModule L.sheaf ((Scheme.Modules.pushforward f).obj M) ≅
      (Scheme.Modules.pushforward f).obj (Tensor.ProductSheaf.tensorModule (L.pullback f).sheaf M) :=
  (TensorEquivalence.lineBundleTensorEquivalence_objIso L ((Scheme.Modules.pushforward f).obj M)).symm ≪≫
    (EquivalenceRightAdjointCommutation.rightAdjointCommutesWithEquivalences (Scheme.Modules.pullbackPushforwardAdjunction f)
      (TensorEquivalence.lineBundleTensorEquivalence L) (TensorEquivalence.lineBundleTensorEquivalence (L.pullback f))
      (TensorPullbackFunctor.lineBundleTensorPullbackFunctorIso f L)).app M ≪≫
    (Scheme.Modules.pushforward f).mapIso (TensorEquivalence.lineBundleTensorEquivalence_objIso (L.pullback f) M)

def lineBundlePushforwardPullbackIso (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y) :
    Tensor.ProductSheaf.tensorModule L.sheaf ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X)) ≅
      (Scheme.Modules.pushforward f).obj (L.pullback f).sheaf :=
  lineBundleProjectionFormulaIso f L (Line.Bundles.structureModule X) ≪≫
    (Scheme.Modules.pushforward f).mapIso
      (Tensor.ProductSheaf.tensorModuleCommIso (L.pullback f).sheaf (Line.Bundles.structureModule X) ≪≫
        Tensor.ProductSheaf.tensorModuleUnitLeftIso (L.pullback f).sheaf)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ProjectionFormula
