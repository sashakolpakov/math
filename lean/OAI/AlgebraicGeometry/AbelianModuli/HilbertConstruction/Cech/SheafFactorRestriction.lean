/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafDifferential.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Differential
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafSectionCoordinates

/-! # Sheaf Factor Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafFactorRestriction.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)

theorem cechTermFactorRestrictionLE {A B : Opens X} (h : A ≤ B)
    (V : Opens X) :
    A.isOpenEmbedding.functor.obj ((Opens.map A.inclusion').obj V) ≤
      B.isOpenEmbedding.functor.obj ((Opens.map B.inclusion').obj V) := by
  simpa only [Opens.functor_map_eq_inf] using inf_le_inf_left V h

/-- Restriction from the restriction-pushforward factor for `B` to the factor for a
smaller open `A`. -/
noncomputable def cechTermFactorRestriction {A B : Opens X} (h : A ≤ B) :
    (TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat B.isOpenEmbedding ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat B.inclusion').obj F ⟶
      (TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat A.isOpenEmbedding ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat A.inclusion').obj F :=
  ObjectProperty.homMk
    { app := fun V =>
        F.obj.map (homOfLE (cechTermFactorRestrictionLE h V.unop)).op
      naturality := by
        intro V W f
        change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
        rw [← F.obj.map_comp, ← F.obj.map_comp]
        rfl }

noncomputable def cechOpenFactorSectionsIso (A V : Opens X) :
    ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat A.isOpenEmbedding ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat A.inclusion').obj F).obj.obj (op V) ≅
      F.obj.obj (op (V ⊓ A)) :=
  F.obj.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf A V)))

theorem cechOpenFactorSectionsIso_hom (A V : Opens X) :
    (cechOpenFactorSectionsIso F A V).hom =
      ((eqToIso (by rw [TopologicalSheafRestriction.IntrinsicCech.toRestrict_obj_obj_obj, Opens.functor_map_eq_inf])) :
        ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat A.isOpenEmbedding ⋙
          TopCat.Sheaf.pushforward AddCommGrpCat A.inclusion').obj F).obj.obj (op V) ≅
            F.obj.obj (op (V ⊓ A))).hom := by
  rw [cechOpenFactorSectionsIso, Functor.mapIso_hom, eqToIso.hom, eqToIso.hom,
    eqToHom_map]
  cat_disch

theorem cechTermFactorRestriction_sections_mapIso {A B : Opens X}
    (h : A ≤ B) (V : Opens X)
    (x : ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat B.isOpenEmbedding ⋙
      TopCat.Sheaf.pushforward AddCommGrpCat B.inclusion').obj F).obj.obj (op V)) :
    (cechOpenFactorSectionsIso F A V).hom
        ((cechTermFactorRestriction F h).hom.app (op V) x) =
      F.obj.map (homOfLE (inf_le_inf_left V h)).op
        ((cechOpenFactorSectionsIso F B V).hom x) := by
  have hmorph :
      F.obj.map (homOfLE (cechTermFactorRestrictionLE h V)).op ≫
          F.obj.map (eqToHom (congrArg op (Opens.functor_map_eq_inf A V))) =
        F.obj.map (eqToHom (congrArg op (Opens.functor_map_eq_inf B V))) ≫
          F.obj.map (homOfLE (inf_le_inf_left V h)).op := by
    rw [← F.obj.map_comp, ← F.obj.map_comp]
    exact congrArg F.obj.map (Subsingleton.elim _ _)
  change (F.obj.map (homOfLE (cechTermFactorRestrictionLE h V)).op ≫
      F.obj.map (eqToHom (congrArg op (Opens.functor_map_eq_inf A V)))) x =
    (F.obj.map (eqToHom (congrArg op (Opens.functor_map_eq_inf B V))) ≫
      F.obj.map (homOfLE (inf_le_inf_left V h)).op) x
  exact ConcreteCategory.congr_hom hmorph x

/-- On sections over `V`, `cechTermFactorRestriction` is the usual restriction
`F(V ∩ B) → F(V ∩ A)`. -/
theorem cechTermFactorRestriction_apply {A B : Opens X} (h : A ≤ B) (V : Opens X)
    (x : ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat B.isOpenEmbedding ⋙
      TopCat.Sheaf.pushforward AddCommGrpCat B.inclusion').obj F).obj.obj (op V)) :
    ((eqToIso (by rw [TopologicalSheafRestriction.IntrinsicCech.toRestrict_obj_obj_obj, Opens.functor_map_eq_inf])) :
      ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat A.isOpenEmbedding ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat A.inclusion').obj F).obj.obj (op V) ≅
          F.obj.obj (op (V ⊓ A))).hom
        ((cechTermFactorRestriction F h).hom.app (op V) x) =
      F.obj.map (homOfLE (inf_le_inf_left V h)).op
        (((eqToIso (by rw [TopologicalSheafRestriction.IntrinsicCech.toRestrict_obj_obj_obj, Opens.functor_map_eq_inf])) :
          ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat B.isOpenEmbedding ⋙
            TopCat.Sheaf.pushforward AddCommGrpCat B.inclusion').obj F).obj.obj (op V) ≅
              F.obj.obj (op (V ⊓ B))).hom x) := by
  rw [← cechOpenFactorSectionsIso_hom, ← cechOpenFactorSectionsIso_hom]
  exact cechTermFactorRestriction_sections_mapIso F h V x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafFactorRestriction.IntrinsicCech
