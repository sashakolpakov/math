import OAI.RepresentationTheory.Theta.Geometric.DisjointLineIsoGluing

/-! # Locally Translated Line Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric.LocallyTranslatedLineIso

noncomputable section

/-! A line-bundle comparison for maps related by locally constant
translations is glued from actual translated pullback isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def translatedMapLineIso {X T : Scheme.{u}} (M : X.Modules) (t : X ⟶ X)
    (e : (Scheme.Modules.pullback t).obj M ≅ M) (x y : T ⟶ X) (h : y = x ≫ t) :
    (Scheme.Modules.pullback y).obj M ≅ (Scheme.Modules.pullback x).obj M :=
  (Scheme.Modules.pullbackCongr h).app M ≪≫ ((Scheme.Modules.pullbackComp x t).app M).symm ≪≫
    (Scheme.Modules.pullback x).mapIso e

def restrictedTranslatedMapLineIso {X T : Scheme.{u}} (M : X.Modules) (t : X ⟶ X)
    (e : (Scheme.Modules.pullback t).obj M ≅ M) (x y : T ⟶ X) (U : T.Opens)
    (h : U.ι ≫ y = (U.ι ≫ x) ≫ t) :
    (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pullback y).obj M) ≅
      (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pullback x).obj M) :=
  (Scheme.Modules.pullbackComp U.ι y).app M ≪≫
    translatedMapLineIso M t e (U.ι ≫ x) (U.ι ≫ y) h ≪≫
      ((Scheme.Modules.pullbackComp U.ι x).app M).symm

theorem exists_iso_of_locally_translated_maps {X T : Scheme.{u}} (M : X.Modules)
    {I : Type u} (c : LocallyConstant T I) (t : I → (X ⟶ X))
    (e : ∀ a, (Scheme.Modules.pullback (t a)).obj M ≅ M) (x y : T ⟶ X)
    (h : ∀ a, (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).ι ≫ y =
      ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).ι ≫ x) ≫ t a) :
    ∃ g : (Scheme.Modules.pullback y).obj M ≅ (Scheme.Modules.pullback x).obj M,
      ∀ a, (Scheme.Modules.pullback (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).ι).map g.hom =
        (restrictedTranslatedMapLineIso M (t a) (e a) x y (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a) (h a)).hom :=
  DisjointLineIsoGluing.exists_moduleIso_on_locallyConstant_fibers _ _ c
    (fun a => restrictedTranslatedMapLineIso M (t a) (e a) x y (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a) (h a))

end

end OAI.RepresentationTheory.Theta.Geometric.LocallyTranslatedLineIso
