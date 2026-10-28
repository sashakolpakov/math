import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedFormulaPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelTrivialization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

/-! # Line Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.LineTransport

noncomputable section

/-! The actual Poincare zero frame and inducing-line formula give transport along a killed subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelTrivialization OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

variable {S : Scheme.{u}} {H A Z : Over S} [GrpObj A] [GrpObj Z]
  (i : H ⟶ A) (φ : A ⟶ Z) (hi : i ≫ φ = 1)
  (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (normalized : (Scheme.Modules.pullback (Poincare.KernelTrivialization.zeroSection (Z := Z) (X := A)).left).obj P.sheaf ≅
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
  (formula : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine P φ).sheaf (L.pullback (fst A A).left).sheaf)
    (L.pullback (snd A A).left).sheaf ≅ (L.pullback μ[A].left).sheaf)

/-- Insert the canonical Poincare frame into the actual original inducing-line formula. -/
def productIso :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      ((Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj (L.pullback (fst A A).left).sheaf)
      ((Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj (L.pullback (snd A A).left).sheaf) ≅
      (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj (L.pullback μ[A].left).sheaf :=
  FramedFormulaPullback.productIso (i ⊗ₘ 𝟙 A).left (FirstBiextensionFactor.familyLine P φ).sheaf
    (L.pullback (fst A A).left).sheaf (L.pullback (snd A A).left).sheaf (L.pullback μ[A].left).sheaf
    (FirstBiextensionFactor.familyLine P φ).isLine (L.pullback (fst A A).left).locallyTrivial
    (L.pullback (snd A A).left).locallyTrivial formula (Poincare.KernelTrivialization.kernelFrame i φ hi P normalized)

/-- The first source factor is the subgroup-restricted line pulled to the product. -/
def firstFactorIso :
    (Scheme.Modules.pullback (fst H A).left).obj (L.pullback i.left).sheaf ≅
      (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj (L.pullback (fst A A).left).sheaf :=
  (Scheme.Modules.pullbackComp (fst H A).left i.left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr
      (congrArg Over.Hom.left (tensorHom_fst i (𝟙 A))).symm).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp (i ⊗ₘ 𝟙 A).left (fst A A).left).symm.app L.sheaf

/-- The second source factor is the original line at the starting point. -/
def secondFactorIso :
    (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj (L.pullback (snd A A).left).sheaf ≅
      (L.pullback (snd H A).left).sheaf :=
  (Scheme.Modules.pullbackComp (i ⊗ₘ 𝟙 A).left (snd A A).left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left
      ((tensorHom_snd i (𝟙 A)).trans (Category.comp_id _)))).app L.sheaf

/-- A frame of the subgroup line gives a genuine global translation isomorphism of the inducing line. -/
def translationIso (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule H.left ≅ (L.pullback i.left).sheaf) :
    (L.pullback (snd H A).left).sheaf ≅ (L.pullback (((i ⊗ₘ 𝟙 A) ≫ μ[A]).left)).sheaf :=
  (secondFactorIso i L).symm ≪≫
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso _).symm ≪≫
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (FrameRatioPullback.pullFrame (fst H A).left s ≪≫ firstFactorIso i L) (Iso.refl _) ≪≫
    productIso i φ hi P normalized L formula ≪≫
    (Scheme.Modules.pullbackComp (i ⊗ₘ 𝟙 A).left μ[A].left).app L.sheaf

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.LineTransport
