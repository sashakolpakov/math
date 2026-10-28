import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.SquareComponents
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.RecoverySquares

/-! # Square Recovery Formula -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SquareRecoveryFormula

noncomputable section

/-!
# Compatible native square recovery agrees with the explicit geometric recovery
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- Reversing a geometric equality reverses its actual pullback isomorphism. -/
theorem pullbackCongr_symm {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (Scheme.Modules.pullbackCongr h.symm).symm = Scheme.Modules.pullbackCongr h := by
  cases h
  rfl

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

variable {S : Scheme.{u}} {X Y X' Y' : Over S} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (hf : f' ≫ iY = iX ≫ f)
  (D : (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => f))
  (L : Line.Bundles.LineBundle X.left) (R : Line.Bundles.LineBundle Y.left)
  (hL : L.sheaf = D.obj PUnit.unit)
  (e : (Scheme.Modules.pullback f.left).obj R.sheaf ≅ L.sheaf)

/-- The inverse composition path has the explicit equality-then-composition form of geometric recovery. -/
theorem composition_path :
    (Scheme.Modules.pullbackComp f'.left iY.left).app R.sheaf ≪≫
      ((Scheme.Modules.pullbackComp iX.left f.left ≪≫
        Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hf.symm)).app R.sheaf).symm ≪≫
      (Scheme.Modules.pullback iX.left).mapIso e =
    Product.RecoverySquares.recoveryIso f.left f'.left iX.left iY.left
      (congrArg Over.Hom.left hf) L R e := by
  have hc := congrArg (fun k => k.app R.sheaf) (pullbackCongr_symm (congrArg Over.Hom.left hf))
  apply Iso.ext
  have hc' := congrArg Iso.hom hc
  change (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hf.symm)).inv.app R.sheaf =
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hf)).hom.app R.sheaf at hc'
  simp only [Product.RecoverySquares.recoveryIso, Iso.trans_hom, Iso.symm_hom,
    NatIso.trans_app, Iso.trans_inv, Functor.mapIso_hom, Category.assoc]
  exact congrArg (fun a => (Scheme.Modules.pullbackComp f'.left iY.left).hom.app R.sheaf ≫ a ≫
    (Scheme.Modules.pullbackComp iX.left f.left).inv.app R.sheaf ≫ (Scheme.Modules.pullback iX.left).map e.hom) hc'

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SquareRecoveryFormula
