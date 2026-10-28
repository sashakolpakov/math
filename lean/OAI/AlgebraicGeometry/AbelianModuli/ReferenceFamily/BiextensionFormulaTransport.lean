import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Biextension Formula Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionFormulaTransport

noncomputable section

/-! Transport the genuine Poincare tensor formula through an actual
group-scheme isomorphism, keeping all pullbacks and tensor sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

def lineBundlePullbackSquareIso {W X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : X ⟶ W) (d : W ⟶ Z) (h : a ≫ b = c ≫ d) (L : HilbertConstruction.Line.Bundles.LineBundle Z) :
    (L.pullback b |>.pullback a).sheaf ≅ (L.pullback d |>.pullback c).sheaf :=
  (Scheme.Modules.pullbackComp a b).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app L.sheaf ≪≫
      (Scheme.Modules.pullbackComp c d).symm.app L.sheaf

def biextensionFormula_transport {S : Scheme.{0}} (X Y : Over S)
    [GrpObj X] [GrpObj Y] (f : X ⟶ Y) [IsIso f] [IsMonHom f]
    (L : HilbertConstruction.Line.Bundles.LineBundle Y.left) (B : HilbertConstruction.Line.Bundles.LineBundle (Y ⊗ Y).left)
    (e : ((B.tensor (L.pullback (fst Y Y).left)).tensor (L.pullback (snd Y Y).left)).sheaf ≅
      (L.pullback (MonObj.mul (X := Y)).left).sheaf) :
    (((B.pullback (f ⊗ₘ f).left).tensor ((L.pullback f.left).pullback (fst X X).left)).tensor
      ((L.pullback f.left).pullback (snd X X).left)).sheaf ≅
        ((L.pullback f.left).pullback (MonObj.mul (X := X)).left).sheaf := by
  let f₂ := f ⊗ₘ f
  let : IsIso f₂ := inferInstanceAs (IsIso (f ⊗ₘ f))
  let : IsIso f₂.left := inferInstanceAs (IsIso ((Over.forget S).map f₂))
  let Q₀ := B.sheaf
  let Q₁ := (L.pullback (fst Y Y).left).sheaf
  let Q₂ := (L.pullback (snd Y Y).left).sheaf
  let e₁ := lineBundlePullbackSquareIso (fst X X).left f.left f₂.left (fst Y Y).left
    (Over.tensorHom_left_fst _ _ _ _).symm L
  let e₂ := lineBundlePullbackSquareIso (snd X X).left f.left f₂.left (snd Y Y).left
    (Over.tensorHom_left_snd _ _ _ _).symm L
  exact HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
      (HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) e₁ ≪≫ (HilbertConstruction.Tensor.ProductBaseChange.tensorModulePullbackIso f₂.left Q₀ Q₁).symm) e₂ ≪≫
    (HilbertConstruction.Tensor.ProductBaseChange.tensorModulePullbackIso f₂.left (HilbertConstruction.Tensor.ProductSheaf.tensorModule Q₀ Q₁) Q₂).symm ≪≫
    (Scheme.Modules.pullback f₂.left).mapIso e ≪≫
    lineBundlePullbackSquareIso f₂.left (MonObj.mul (X := Y)).left
      (MonObj.mul (X := X)).left f.left (congrArg Over.Hom.left (IsMonHom.mul_hom f)).symm L

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionFormulaTransport
