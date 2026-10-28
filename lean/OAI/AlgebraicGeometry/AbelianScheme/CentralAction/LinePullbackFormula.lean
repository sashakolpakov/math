import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LinePullHom

/-! # Line Pullback Formula -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LinePullbackFormula

noncomputable section

/-! The native pullHom operation is the explicit geometric pullback
comparison used in the normalized Poincare construction. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Construction

universe u
variable {S : Scheme.{u}} {X T W : Over S}

def linePullbackSquareIso (f : T ⟶ X) (g : W ⟶ T) (f' : W ⟶ X) (hf : g ≫ f = f') :
    Scheme.Modules.pullback f.left ⋙ Scheme.Modules.pullback g.left ≅
      Scheme.Modules.pullback f'.left :=
  Scheme.Modules.pullbackComp g.left f.left ≪≫
    Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hf)

theorem linePullHom_formula (f : T ⟶ X) (g : W ⟶ T) (f' : W ⟶ X) (hf : g ≫ f = f')
    (L M : X.left.Modules)
    (a : (Scheme.Modules.pullback f.left).obj L ⟶ (Scheme.Modules.pullback f.left).obj M) :
    pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) (M₁ := L) (M₂ := M) a g f' f' hf hf =
      (linePullbackSquareIso f g f' hf).inv.app L ≫
        (Scheme.Modules.pullback g.left).map a ≫
          (linePullbackSquareIso f g f' hf).hom.app M := by
  subst f'
  simp only [pullHom]
  rfl

def lineSquareNormalization {A B : Over S} (f : T ⟶ X) (z : A ⟶ T)
    (w : B ⟶ X) (j : A ⟶ B) (h : z ≫ f = j ≫ w) (L : X.left.Modules)
    (l : (Scheme.Modules.pullback w.left).obj L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left) :
    (Scheme.Modules.pullback z.left).obj ((Scheme.Modules.pullback f.left).obj L) ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left :=
  (linePullbackSquareIso f z (j ≫ w) h).app L ≪≫
    ((linePullbackSquareIso w j (j ≫ w) rfl).app L).symm ≪≫
      (Scheme.Modules.pullback j.left).mapIso l ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso j.left

/-- Concrete normalization equations imply the native pullHom equation
used by the already proved overlap compatibility theorem. -/
theorem linePullHom_of_square_normalization {A B : Over S}
    (f : T ⟶ X) (z : A ⟶ T) (w : B ⟶ X) (j : A ⟶ B) (h : z ≫ f = j ≫ w)
    (L M : X.left.Modules)
    (l : (Scheme.Modules.pullback w.left).obj L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left)
    (m : (Scheme.Modules.pullback w.left).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left)
    (a : (Scheme.Modules.pullback f.left).obj L ⟶ (Scheme.Modules.pullback f.left).obj M)
    (hn : (Scheme.Modules.pullback z.left).map a ≫ (lineSquareNormalization f z w j h M m).hom =
      (lineSquareNormalization f z w j h L l).hom) :
    pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) (M₁ := L) (M₂ := M) a z (j ≫ w) (j ≫ w) h h =
      pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) (M₁ := L) (M₂ := M)
        (l.hom ≫ m.inv) j (j ≫ w) (j ≫ w) rfl rfl := by
  rw [linePullHom_formula, linePullHom_formula]
  apply (cancel_epi ((linePullbackSquareIso f z (j ≫ w) h).hom.app L)).mp
  apply (cancel_mono
    ((linePullbackSquareIso w j (j ≫ w) rfl).inv.app M ≫
      (Scheme.Modules.pullback j.left).map m.hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso j.left).hom)).mp
  have hc : (Scheme.Modules.pullback j.left).map (l.hom ≫ m.inv) ≫
      (Scheme.Modules.pullback j.left).map m.hom =
        (Scheme.Modules.pullback j.left).map l.hom := by
    rw [← Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [lineSquareNormalization, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_app_assoc] at hn ⊢
  erw [reassoc_of% hc]
  exact hn

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LinePullbackFormula
