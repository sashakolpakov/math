import Mathlib.Algebra.Homology.Additive

/-! # Functor Transformation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.FunctorTransformation

noncomputable section

/-! The canonical single-complex coordinates commute with a natural
transformation of additive coefficient functors. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasZeroObject B]
  (F G : A ⥤ B) [F.Additive] [G.Additive] (η : F ⟶ G) (M : A) (c : ℕ)

theorem naturality :
    (NatTrans.mapHomologicalComplex η (.up ℕ)).app ((single A (.up ℕ) c).obj M) ≫
        (singleMapHomologicalComplex G (.up ℕ) c).hom.app M =
      (singleMapHomologicalComplex F (.up ℕ) c).hom.app M ≫
        (single B (.up ℕ) c).map (η.app M) := by
  apply to_single_hom_ext
  simp only [comp_f, singleMapHomologicalComplex_hom_app_self, single_map_f_self]
  change η.app _ ≫ (G.map (singleObjXSelf (.up ℕ) c M).hom ≫
      (singleObjXSelf (.up ℕ) c (G.obj M)).inv) =
    (F.map (singleObjXSelf (.up ℕ) c M).hom ≫
      (singleObjXSelf (.up ℕ) c (F.obj M)).inv) ≫
        ((singleObjXSelf (.up ℕ) c (F.obj M)).hom ≫ η.app M ≫
          (singleObjXSelf (.up ℕ) c (G.obj M)).inv)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← η.naturality, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.FunctorTransformation
