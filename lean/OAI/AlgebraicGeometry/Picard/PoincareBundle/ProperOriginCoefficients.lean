import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions

/-! # Proper Origin Coefficients -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperOriginCoefficients

noncomputable section

/-! Proper group geometry makes the scalar coefficient of an origin comparison independent of the point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios

/-- A global unit pulled from the base takes the same value at all test points over that base. -/
theorem unit_pullback_eq {X Y T : Scheme.{u}} (p : X ⟶ Y) [IsIso p.appTop]
    (x y : T ⟶ X) (h : x ≫ p = y ≫ p) (r : Γ(X, ⊤)ˣ) :
    Units.map x.appTop.hom.toMonoidHom r = Units.map y.appTop.hom.toMonoidHom r := by
  let c := Units.map (asIso p.appTop).inv.hom.toMonoidHom r
  have hc : Units.map p.appTop.hom.toMonoidHom c = r := by
    apply Units.ext
    exact ConcreteCategory.congr_hom (asIso p.appTop).inv_hom_id r.val
  calc
    Units.map x.appTop.hom.toMonoidHom r = Units.map x.appTop.hom.toMonoidHom (Units.map p.appTop.hom.toMonoidHom c) :=
      congrArg (Units.map x.appTop.hom.toMonoidHom) hc.symm
    _ = Units.map y.appTop.hom.toMonoidHom (Units.map p.appTop.hom.toMonoidHom c) := by
      apply Units.ext
      change (x ≫ p).appTop c.val = (y ≫ p).appTop c.val
      rw [h]
    _ = Units.map y.appTop.hom.toMonoidHom r := congrArg (Units.map y.appTop.hom.toMonoidHom) hc

/-- Ratios of actual line comparisons have identical coefficients at every pair of test points. -/
theorem ratio_pullback_eq {X Y T : Scheme.{u}} (p : X ⟶ Y) [IsIso p.appTop]
    (x y : T ⟶ X) (h : x ≫ p = y ≫ p) {M N : X.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (e f : M ≅ N) :
    Line.IsoRatios.ratio (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback x M hM) ((Scheme.Modules.pullback x).mapIso e) ((Scheme.Modules.pullback x).mapIso f) =
      Line.IsoRatios.ratio (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback y M hM) ((Scheme.Modules.pullback y).mapIso e) ((Scheme.Modules.pullback y).mapIso f) := by
  rw [Line.IsoRatios.ratio_pullback hM x, Line.IsoRatios.ratio_pullback hM y]
  exact unit_pullback_eq p x y h (Line.IsoRatios.ratio hM e f)

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

/-- Proper smooth connected group geometry supplies the base-function isomorphism internally. -/
theorem group_ratio_eq {T : Over (Spec (.of k))} (x y : T ⟶ A)
    {M N : A.left.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (e f : M ≅ N) :
    Line.IsoRatios.ratio (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback x.left M hM) ((Scheme.Modules.pullback x.left).mapIso e)
        ((Scheme.Modules.pullback x.left).mapIso f) =
      Line.IsoRatios.ratio (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback y.left M hM) ((Scheme.Modules.pullback y.left).mapIso e)
        ((Scheme.Modules.pullback y.left).mapIso f) := by
  have : IsIso A.hom.appTop := Homomorphisms.ProperGroupFunctions.Construction.properGroup_appTop_isIso A
  exact ratio_pullback_eq A.hom x.left y.left ((Over.w x).trans (Over.w y).symm) hM e f

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperOriginCoefficients
