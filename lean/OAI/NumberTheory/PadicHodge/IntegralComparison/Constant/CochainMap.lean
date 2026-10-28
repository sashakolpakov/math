import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Functor.Category

/-! # Cochain Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.CochainMap

noncomputable section

/-! Postcomposition of an actual constant-presheaf cochain map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms D] [HasZeroMorphisms E]
  (G : D ⥤ E) [G.PreservesZeroMorphisms]

local instance const_zero_D : (Functor.const C : D ⥤ C ⥤ D).PreservesZeroMorphisms where
  map_zero _ _ := rfl
local instance const_zero_E : (Functor.const C : E ⥤ C ⥤ E).PreservesZeroMorphisms where
  map_zero _ _ := rfl
local instance whisker_zero : ((Functor.whiskeringRight C D E).obj G).PreservesZeroMorphisms where
  map_zero X Y := by
    apply NatTrans.ext
    funext V
    exact G.map_zero _ _

variable (M : CochainComplex D ℕ) (P : CochainComplex (C ⥤ D) ℕ)
  (a : ((Functor.const C).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)

def map : ((Functor.const C).mapHomologicalComplex (.up ℕ)).obj
    ((G.mapHomologicalComplex (.up ℕ)).obj M) ⟶
      ((((Functor.whiskeringRight C D E).obj G).mapHomologicalComplex (.up ℕ)).obj P) where
  f q :=
    { app V := G.map ((a.f q).app V)
      naturality V W f := by
        change 𝟙 _ ≫ G.map ((a.f q).app W) =
          G.map ((a.f q).app V) ≫ G.map ((P.X q).map f)
        have h : (a.f q).app W = (a.f q).app V ≫ (P.X q).map f :=
          (Category.id_comp _).symm.trans ((a.f q).naturality f)
        exact (Category.id_comp _).trans
          ((congrArg G.map h).trans (G.map_comp _ _)) }
  comm' i j _ := by
    apply NatTrans.ext
    funext V
    change G.map ((a.f i).app V) ≫ G.map ((P.d i j).app V) =
      G.map (M.d i j) ≫ G.map ((a.f j).app V)
    exact (G.map_comp _ _).symm.trans
      ((congrArg G.map (congrArg (fun b => b.app V) (a.comm i j))).trans
        (G.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.CochainMap
