import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareModuleMaps

/-! # Associativity Components -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityComponents

noncomputable section

/-! The associativity comparison for three module-sheaf pullbacks, on components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {W X Y Z : Scheme.{u}}

theorem modulePullbackCongr_hom_app {a b : X ⟶ Y} (h : a = b) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M =
      eqToHom (congrArg (fun f : X ⟶ Y => (Scheme.Modules.pullback f).obj M) h) := by
  subst b
  rfl

theorem modulePullback_associativity_components (a : W ⟶ X) (b : X ⟶ Y) (f : Y ⟶ Z)
    (M : Z.Modules) :
    (Scheme.Modules.pullbackComp a (b ≫ f)).inv.app M ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b f).inv.app M) ≫
        (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullbackComp (a ≫ b) f).hom.app M =
      (Scheme.Modules.pullbackCongr (Category.assoc a b f).symm).hom.app M := by
  have h := congr_app (Scheme.Modules.pseudofunctor_associativity a b f) M
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, modulePullbackCongr_hom_app, eqToHom_app] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityComponents
