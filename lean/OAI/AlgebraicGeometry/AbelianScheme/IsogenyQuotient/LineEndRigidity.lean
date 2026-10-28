import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ProductIsomorphisms

/-! # Line End Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineEndRigidity.Construction

noncomputable section

/-! A line endomorphism is the identity if its pullback is the
identity under any fiber comparison that preserves global functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

theorem lineEnd_eq_id_of_pullback_conjugate {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p.appTop]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (f : L.sheaf ⟶ L.sheaf) {M : X.Modules}
    (e : (Scheme.Modules.pullback p).obj L.sheaf ≅ M)
    (h : e.inv ≫ (Scheme.Modules.pullback p).map f ≫ e.hom = 𝟙 M) : f = 𝟙 L.sheaf := by
  have hm : (Scheme.Modules.pullback p).map f = 𝟙 _ := by
    apply (cancel_epi e.inv).mp
    apply (cancel_mono e.hom).mp
    simpa only [Category.assoc, Category.id_comp, e.inv_hom_id] using h
  apply (Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.endPullbackEquiv p L).injective
  rw [Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.endPullbackEquiv_apply,
    Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.endPullbackEquiv_apply]
  exact hm.trans ((Scheme.Modules.pullback p).map_id L.sheaf).symm

theorem lineEnd_eq_id_of_origin {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle T.left) (f : L.sheaf ⟶ L.sheaf)
    {M : (𝟙_ (Over (Spec (.of k)))).left.Modules}
    (e : (Scheme.Modules.pullback η[T].left).obj L.sheaf ≅ M)
    (h : e.inv ≫ (Scheme.Modules.pullback η[T].left).map f ≫ e.hom = 𝟙 M) : f = 𝟙 L.sheaf := by
  have : IsIso η[T].left.appTop := Poincare.ProductIsomorphisms.Construction.origin_appTop_isIso T
  exact lineEnd_eq_id_of_pullback_conjugate η[T].left L f e h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineEndRigidity.Construction
