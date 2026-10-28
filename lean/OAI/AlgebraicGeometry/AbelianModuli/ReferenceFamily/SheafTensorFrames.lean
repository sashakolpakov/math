import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafTensorUnit
import OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame

/-! # Sheaf Tensor Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafTensorFrames

noncomputable section

/-! Tensor frames on actual module sheaves have the product transition
units required by the logarithmic Chern-class construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame.Construction (moduleSheafSectionIso frameTransitionUnit)

variable {X : Scheme.{0}} {M N : X.Modules}

def sheafSectionFrame (e : M ≅ HilbertConstruction.Line.Bundles.structureModule X) (U : X.Opens) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U) := DivisorClass.Chern.FramesFrame.Construction.moduleSheafSectionIso e U

def tensorSheafFrame (e : M ≅ HilbertConstruction.Line.Bundles.structureModule X) (f : N ≅ HilbertConstruction.Line.Bundles.structureModule X) :
    HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ≅ HilbertConstruction.Line.Bundles.structureModule X := SheafTensorMaps.sheafTensorIso e f ≪≫ SheafTensorUnit.sheafTensorUnitIso X

theorem tensorSheafFrame_apply (e : M ≅ HilbertConstruction.Line.Bundles.structureModule X) (f : N ≅ HilbertConstruction.Line.Bundles.structureModule X)
    (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
    sheafSectionFrame (tensorSheafFrame e f) U ((SheafTensorMaps.tensorBilinear M N).app U x y) =
      sheafSectionFrame e U x * sheafSectionFrame f U y := by
  change (SheafTensorUnit.tensorUnitHom X).app U
    ((SheafTensorMaps.sheafTensorMap e.hom f.hom).app U ((SheafTensorMaps.tensorBilinear M N).app U x y)) = _
  rw [SheafTensorMaps.sheafTensorMap_apply]
  exact SheafTensorUnit.tensorUnitHom_apply X U (sheafSectionFrame e U x) (sheafSectionFrame f U y)

theorem tensorSheafFrame_generator (e : M ≅ HilbertConstruction.Line.Bundles.structureModule X) (f : N ≅ HilbertConstruction.Line.Bundles.structureModule X)
    (U : X.Opens) :
    (sheafSectionFrame (tensorSheafFrame e f) U).symm 1 =
      (SheafTensorMaps.tensorBilinear M N).app U ((sheafSectionFrame e U).symm 1) ((sheafSectionFrame f U).symm 1) := by
  apply (sheafSectionFrame (tensorSheafFrame e f) U).injective
  rw [LinearEquiv.apply_symm_apply, tensorSheafFrame_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, one_mul]

theorem tensorSheafFrame_transition
    (e e' : M ≅ HilbertConstruction.Line.Bundles.structureModule X) (f f' : N ≅ HilbertConstruction.Line.Bundles.structureModule X) (U : X.Opens) :
    DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (sheafSectionFrame (tensorSheafFrame e f) U)
      (sheafSectionFrame (tensorSheafFrame e' f') U) =
        DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (sheafSectionFrame e U) (sheafSectionFrame e' U) *
          DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (sheafSectionFrame f U) (sheafSectionFrame f' U) := by
  apply Units.ext
  change sheafSectionFrame (tensorSheafFrame e f) U
    ((sheafSectionFrame (tensorSheafFrame e' f') U).symm 1) =
      sheafSectionFrame e U ((sheafSectionFrame e' U).symm 1) *
        sheafSectionFrame f U ((sheafSectionFrame f' U).symm 1)
  rw [tensorSheafFrame_generator, tensorSheafFrame_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafTensorFrames
