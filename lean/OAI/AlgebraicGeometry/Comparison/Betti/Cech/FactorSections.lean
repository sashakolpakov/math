import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechFunctor
import Mathlib.CategoryTheory.Sites.GlobalSections

/-! # Factor Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.FactorSections

noncomputable section

/-! Global sections of the actual restriction–pushforward Čech factor are sections on its open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}}

abbrev sheafTopSections : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)

instance sheafTopSections_additive : (sheafTopSections (X := X)).Additive where
  map_add := by
    intro F G f g
    rfl

instance sheafTopSections_preservesLimits :
    PreservesLimitsOfSize.{0, 0} (sheafTopSections (X := X)) :=
  inferInstanceAs (PreservesLimitsOfSize.{0, 0}
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op ⊤)))

def cechFactorGlobalSectionsIso (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechFactorPresheaf F ⋙ sheafTopSections ≅ F.obj :=
  NatIso.ofComponents
    (fun A => F.obj.mapIso (eqToIso (congrArg op (Opens.isOpenEmbedding_obj_top A.unop))))
    (fun i => by
      change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      exact congrArg F.obj.map (Subsingleton.elim _ _))

theorem cechFactorGlobalSectionsIso_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G) (A : (Opens X)ᵒᵖ) :
    sheafTopSections.map ((Betti.Sheaf.CechFunctor.sheafCechFactorMap f).app A) ≫
        (cechFactorGlobalSectionsIso G).hom.app A =
      (cechFactorGlobalSectionsIso F).hom.app A ≫ f.hom.app A := by
  exact (f.hom.naturality
    (eqToHom (congrArg op (Opens.isOpenEmbedding_obj_top A.unop)))).symm

def sheafCechFactorGlobalFunctorIso :
    Betti.Sheaf.CechFunctor.sheafCechFactorFunctor (X := X) ⋙
        (Functor.whiskeringRight (Opens X)ᵒᵖ (TopCat.Sheaf AddCommGrpCat.{0} X) AddCommGrpCat.{0}).obj
          sheafTopSections ≅ TopCat.Sheaf.forget AddCommGrpCat.{0} X :=
  NatIso.ofComponents cechFactorGlobalSectionsIso (fun f => by
    apply NatTrans.ext
    funext A
    exact cechFactorGlobalSectionsIso_naturality f A)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.FactorSections
