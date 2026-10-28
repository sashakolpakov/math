import OAI.RepresentationTheory.Theta.Geometric.TensorModulePullback

/-! # Poincare Formula Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.PoincareFormulaPullback

noncomputable section

/-! A native tensor formula for line bundles pulls back across a commuting
diagram, with all tensor products and pullbacks taken on actual module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def lineBundleSquarePullbackIso {W X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ W) (d : W ⟶ Z)
    (h : a ≫ b = c ≫ d) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Z) :
    ((L.pullback b).pullback a).sheaf ≅ ((L.pullback d).pullback c).sheaf :=
  (Scheme.Modules.pullbackComp a b).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp c d).symm.app L.sheaf

def tensorFormulaPullbackIso {X Z X' Z' : Scheme.{u}}
    (f : X' ⟶ X) (h : Z' ⟶ Z) (p₁ p₂ m : Z ⟶ X) (p₁' p₂' m' : Z' ⟶ X')
    (h₁ : p₁' ≫ f = h ≫ p₁) (h₂ : p₂' ≫ f = h ≫ p₂) (hm : h ≫ m = m' ≫ f)
    (B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Z) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (e : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule B.sheaf (L.pullback p₁).sheaf) (L.pullback p₂).sheaf ≅
      (L.pullback m).sheaf) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (B.pullback h).sheaf ((L.pullback f).pullback p₁').sheaf)
      ((L.pullback f).pullback p₂').sheaf ≅ ((L.pullback f).pullback m').sheaf :=
  AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) (lineBundleSquarePullbackIso p₁' f h p₁ h₁ L) ≪≫
      (TensorModulePullback.tensorModulePullbackIso h B.sheaf (L.pullback p₁).sheaf).symm)
    (lineBundleSquarePullbackIso p₂' f h p₂ h₂ L) ≪≫
    (TensorModulePullback.tensorModulePullbackIso h (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule B.sheaf (L.pullback p₁).sheaf) (L.pullback p₂).sheaf).symm ≪≫
    (Scheme.Modules.pullback h).mapIso e ≪≫ lineBundleSquarePullbackIso h m m' f hm L

end

end OAI.RepresentationTheory.Theta.Geometric.PoincareFormulaPullback
