import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineEndRigidity

/-! # Line Hom Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineHomRigidity.Construction

noncomputable section

/-! Pullback detects arbitrary maps between isomorphic line sheaves
when it preserves global functions. No invertibility of the compared
maps is needed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

theorem lineHom_eq_of_pullback {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p.appTop]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) {M : Y.Modules} (e : L.sheaf ≅ M) (f g : L.sheaf ⟶ M)
    (h : (Scheme.Modules.pullback p).map f = (Scheme.Modules.pullback p).map g) : f = g := by
  apply (cancel_mono e.inv).mp
  apply (Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.endPullbackEquiv p L).injective
  rw [Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.endPullbackEquiv_apply,
    Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.endPullbackEquiv_apply,
    (Scheme.Modules.pullback p).map_comp, (Scheme.Modules.pullback p).map_comp, h]

theorem lineHom_eq_of_origin {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle T.left) {M : T.left.Modules} (e : L.sheaf ≅ M) (f g : L.sheaf ⟶ M)
    (h : (Scheme.Modules.pullback η[T].left).map f = (Scheme.Modules.pullback η[T].left).map g) : f = g := by
  have : IsIso η[T].left.appTop := Poincare.ProductIsomorphisms.Construction.origin_appTop_isIso T
  exact lineHom_eq_of_pullback η[T].left L e f g h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineHomRigidity.Construction
