import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Bundles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.Bundles

noncomputable section

/-! A morphism to the dual gives an actual line bundle by pulling back the normalized Poincare bundle along its graph. This global construction commutes with arbitrary base change; ampleness is not asserted here. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {g : ℕ} {S T : Scheme.{u}} {A : Abelian.Schemes.AbelianScheme g S}
variable (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)

def poincareGraphMap : A.scheme ⟶ D.abelian.scheme ⊗ A.scheme := lift p (𝟙 A.scheme)

theorem poincareGraphMap_fst :
    (poincareGraphMap D p).left ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
      p.left := by
  change (lift p (𝟙 A.scheme)).left ≫ (fst D.abelian.scheme A.scheme).left = p.left
  exact congrArg (fun a => a.left) (lift_fst p (𝟙 A.scheme))

theorem poincareGraphMap_snd :
    (poincareGraphMap D p).left ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
      𝟙 A.scheme.left := by
  change (lift p (𝟙 A.scheme)).left ≫ (snd D.abelian.scheme A.scheme).left = 𝟙 A.scheme.left
  exact congrArg (fun a => a.left) (lift_snd p (𝟙 A.scheme))

def poincareGraphBundle : Line.Bundles.LineBundle A.scheme.left :=
  Line.Bundles.LineBundle.pullback (poincareGraphMap D p).left D.poincare

theorem poincareGraphMap_baseChange (f : T ⟶ S) :
    (poincareGraphMap (D.pullback f) ((Over.pullback f).map p)).left ≫
        (D.poincarePullbackOverMap f).left =
      pullback.fst A.scheme.hom f ≫ (poincareGraphMap D p).left := by
  apply Over.tensorObj_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun a =>
        (poincareGraphMap (D.pullback f) ((Over.pullback f).map p)).left ≫ a)
          (D.poincarePullbackOverMap_left_fst f)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ pullback.fst D.abelian.scheme.hom f)
            (poincareGraphMap_fst (D.pullback f) ((Over.pullback f).map p))).trans
            ((Pullback.Comparisons.overPullback_map_left_fst p f).trans
              ((congrArg (fun a => pullback.fst A.scheme.hom f ≫ a)
                (poincareGraphMap_fst D p).symm).trans
                (Category.assoc _ _ _).symm)))))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun a =>
        (poincareGraphMap (D.pullback f) ((Over.pullback f).map p)).left ≫ a)
          (D.poincarePullbackOverMap_left_snd f)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ pullback.fst A.scheme.hom f)
            (poincareGraphMap_snd (D.pullback f) ((Over.pullback f).map p))).trans
            ((Category.id_comp _).trans
              ((Category.comp_id _).symm.trans
                ((congrArg (fun a => pullback.fst A.scheme.hom f ≫ a)
                  (poincareGraphMap_snd D p).symm).trans
                  (Category.assoc _ _ _).symm))))))

def poincareGraphBundle_baseChangeIso (f : T ⟶ S) :
    (poincareGraphBundle (D.pullback f) ((Over.pullback f).map p)).sheaf ≅
      (Line.Bundles.LineBundle.pullback (pullback.fst A.scheme.hom f) (poincareGraphBundle D p)).sheaf :=
  (Scheme.Modules.pullbackComp (poincareGraphMap (D.pullback f) ((Over.pullback f).map p)).left
    (D.poincarePullbackOverMap f).left).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (poincareGraphMap_baseChange D p f)).app D.poincare.sheaf ≪≫
        (Scheme.Modules.pullbackComp (pullback.fst A.scheme.hom f) (poincareGraphMap D p).left).symm.app D.poincare.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.Bundles
