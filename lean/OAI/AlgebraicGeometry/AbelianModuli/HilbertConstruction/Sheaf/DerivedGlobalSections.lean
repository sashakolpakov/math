/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedDerivedFunctor
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Derived Global Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}}

abbrev J (X : TopCat.{u}) := Opens.grothendieckTopology X

abbrev constantZ (X : TopCat.{u}) :
    CategoryTheory.Sheaf (J X) AddCommGrpCat.{u} :=
  (CategoryTheory.constantSheaf (J X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

abbrev additiveSheafGlobalSectionsFunctor (X : TopCat.{u}) :
    CategoryTheory.Sheaf (J X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.Γ (J X) AddCommGrpCat.{u}

noncomputable local instance : (additiveSheafGlobalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj (J X) AddCommGrpCat.{u}).right_adjoint_additive

def homToGlobalSectionsEquiv
    (F : CategoryTheory.Sheaf (J X) AddCommGrpCat.{u}) :
    (constantZ X ⟶ F) ≃+ ↑((additiveSheafGlobalSectionsFunctor X).obj F) :=
  ((CategoryTheory.constantSheafΓAdj (J X) AddCommGrpCat.{u}).homAddEquiv
      (AddCommGrpCat.of (ULift.{u} ℤ)) F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv ((additiveSheafGlobalSectionsFunctor X).obj F))

lemma homToGlobalSectionsEquiv_naturality
    {F G : CategoryTheory.Sheaf (J X) AddCommGrpCat.{u}}
    (f : constantZ X ⟶ F) (g : F ⟶ G) :
    homToGlobalSectionsEquiv G (f ≫ g) =
      (additiveSheafGlobalSectionsFunctor X).map g (homToGlobalSectionsEquiv F f) := by
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((CategoryTheory.constantSheafΓAdj (J X) AddCommGrpCat.{u}).homEquiv _ _ (f ≫ g)) = _
  rw [(CategoryTheory.constantSheafΓAdj
    (J X) AddCommGrpCat.{u}).homEquiv_naturality_right]
  rfl

/-- Sheaf cohomology agrees with the right-derived functors of global sections. -/
noncomputable def sheafCohomologyAddEquivRightDerived
    (F : CategoryTheory.Sheaf (J X) AddCommGrpCat.{u}) (n : ℕ) :
    CategoryTheory.Sheaf.H F n ≃+ ↑(((additiveSheafGlobalSectionsFunctor X).rightDerived n).obj F) := by
  exact RepresentedDerivedFunctor.DerivedSections.addEquivRightDerived
    (additiveSheafGlobalSectionsFunctor X) (constantZ X) F
    homToGlobalSectionsEquiv
    (fun f g ↦ homToGlobalSectionsEquiv_naturality f g) n

/-- The identification of sheaf cohomology with derived global sections commutes with
morphisms of sheaves. -/
theorem sheafCohomologyAddEquivRightDerived_naturality
    {F G : CategoryTheory.Sheaf (J X) AddCommGrpCat.{u}} (f : F ⟶ G) (n : ℕ) (x : CategoryTheory.Sheaf.H F n) :
    sheafCohomologyAddEquivRightDerived G n (CategoryTheory.Sheaf.H.map f n x) =
      (((additiveSheafGlobalSectionsFunctor X).rightDerived n).map f).hom
        (sheafCohomologyAddEquivRightDerived F n x) := by
  exact RepresentedDerivedFunctor.DerivedSections.addEquivRightDerived_naturality
    (additiveSheafGlobalSectionsFunctor X) (constantZ X) homToGlobalSectionsEquiv
      (fun a b ↦ homToGlobalSectionsEquiv_naturality a b) f n x

/-- The inverse comparison from derived global sections to sheaf cohomology
is natural in the coefficient sheaf. -/
theorem sheafCohomologyAddEquivRightDerived_symm_naturality
    {F G : CategoryTheory.Sheaf (J X) AddCommGrpCat.{u}} (f : F ⟶ G) (n : ℕ)
    (x : ((additiveSheafGlobalSectionsFunctor X).rightDerived n).obj F) :
    (sheafCohomologyAddEquivRightDerived G n).symm
        (((additiveSheafGlobalSectionsFunctor X).rightDerived n).map f x) =
      CategoryTheory.Sheaf.H.map f n ((sheafCohomologyAddEquivRightDerived F n).symm x) := by
  apply (sheafCohomologyAddEquivRightDerived G n).injective
  rw [AddEquiv.apply_symm_apply]
  rw [sheafCohomologyAddEquivRightDerived_naturality]
  rw [AddEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections
