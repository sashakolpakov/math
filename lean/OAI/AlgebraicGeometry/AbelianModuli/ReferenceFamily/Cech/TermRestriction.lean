import OAI.AlgebraicGeometry.SheafCohomology.Cech.Terms

/-! # Term Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.TermRestriction

noncomputable section

/-! The original sheaf-level Cech coordinates commute with restriction
of the ambient algebraic open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open _root_.TopCat.Sheaf

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)

def openCechFactorSectionsIso (A V : Opens X) :
    ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat A.isOpenEmbedding ⋙ pushforward AddCommGrpCat A.inclusion').obj F).obj.obj (op V) ≅
      F.obj.obj (op (V ⊓ A)) :=
  F.obj.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf A V)))

theorem openCechFactorSectionsIso_hom (A V : Opens X) :
    (openCechFactorSectionsIso F A V).hom =
      ((eqToIso (by rw [SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.toRestrict_obj_obj_obj, Opens.functor_map_eq_inf])) :
        ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat A.isOpenEmbedding ⋙ pushforward AddCommGrpCat A.inclusion').obj F).obj.obj (op V) ≅
          F.obj.obj (op (V ⊓ A))).hom := by
  rw [openCechFactorSectionsIso, Functor.mapIso_hom, eqToIso.hom, eqToIso.hom, eqToHom_map]
  cat_disch

theorem openCechFactorSectionsIso_restrict (A : Opens X) {V W : Opens X} (h : W ≤ V)
    (c : ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat A.isOpenEmbedding ⋙ pushforward AddCommGrpCat A.inclusion').obj F).obj.obj (op V)) :
    (openCechFactorSectionsIso F A W).hom
      (((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat A.isOpenEmbedding ⋙ pushforward AddCommGrpCat A.inclusion').obj F).obj.map (homOfLE h).op c) =
      F.obj.map (homOfLE (inf_le_inf_right A h)).op ((openCechFactorSectionsIso F A V).hom c) := by
  change (F.obj.map _ ≫ F.obj.map (eqToHom (congrArg op (Opens.functor_map_eq_inf A W)))) c =
    (F.obj.map (eqToHom (congrArg op (Opens.functor_map_eq_inf A V))) ≫ F.obj.map _) c
  apply ConcreteCategory.congr_hom
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

theorem cechTermCoordinates_restrict {I : Type} (U : I → Opens X) (n : ℕ)
    {V W : Opens X} (h : W ≤ V) (c : (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm F U n).obj.obj (op V)) (i : Fin (n + 1) → I) :
    SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U n W ((SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm F U n).obj.map (homOfLE h).op c) i =
      F.obj.map (homOfLE (inf_le_inf_right (∏ᶜ fun k : Fin (n + 1) => U (i k)) h)).op
        (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U n V c i) := by
  rw [SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv_apply, SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv_apply,
    ← openCechFactorSectionsIso_hom, ← openCechFactorSectionsIso_hom]
  have hp := ConcreteCategory.congr_hom
    ((Pi.π (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermFactor F U n) i).hom.naturality (homOfLE h).op) c
  change (Pi.π (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermFactor F U n) i).hom.app (op W)
      ((SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm F U n).obj.map (homOfLE h).op c) =
    (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermFactor F U n i).obj.map (homOfLE h).op
      ((Pi.π (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermFactor F U n) i).hom.app (op V) c) at hp
  exact (congrArg (openCechFactorSectionsIso F _ W).hom hp).trans
    (openCechFactorSectionsIso_restrict F _ h _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.TermRestriction
