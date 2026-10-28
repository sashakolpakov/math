import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Tensor Local Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorLocalFrames

noncomputable section

/-! On a frame open of a line bundle, tensoring with it is isomorphic to the original module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def tensorModuleRightFrameIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (L : Line.Bundles.LineBundle Y)
    (e : (Scheme.Modules.pullback f).obj L.sheaf ≅ Line.Bundles.structureModule X) :
    (Tensor.ProductSheaf.tensorModule M L.sheaf).restrict f ≅ M.restrict f :=
  Tensor.ProductBaseChange.tensorModuleRestrictIso f M L.sheaf ≪≫
    Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) ((Scheme.Modules.restrictFunctorIsoPullback f).app L.sheaf ≪≫ e) ≪≫
      Tensor.ProductSheaf.tensorModuleCommIso _ _ ≪≫ Tensor.ProductSheaf.tensorModuleUnitLeftIso _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorLocalFrames
