import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SectionCoordinates
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-! # Hom Complex Sections -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.HomComplexSections

noncomputable section

/-! Representing-object cochains are the actual native global sections, with their differential. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf
open _root_.CochainComplex _root_.CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

local instance nativeSectionCoordinates_additive : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}).right_adjoint_additive

variable (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ)

def nativeHomCochainEquiv (n : ℤ) :
    Cochain ((singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) 0).obj (Chern.Sheaf.ResolutionClasses.sheafCohomologySource X)) K n ≃+
      (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).obj (K.X n) :=
  (Cochain.fromSingleEquiv (zero_add n)).trans (SectionCoordinates.nativeSheafHomGlobalEquiv (K.X n))

theorem nativeHomCochainEquiv_fromSingle (n : ℤ) (f : Chern.Sheaf.ResolutionClasses.sheafCohomologySource X ⟶ K.X n) :
    nativeHomCochainEquiv K n (Cochain.fromSingleMk f (zero_add n)) =
      SectionCoordinates.nativeSheafHomGlobalEquiv (K.X n) f := by
  exact congrArg (SectionCoordinates.nativeSheafHomGlobalEquiv (K.X n))
    (Cochain.fromSingleEquiv_fromSingleMk f (zero_add n))

theorem nativeHomCochainEquiv_d (i j : ℤ)
    (c : Cochain ((singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) 0).obj
      (Chern.Sheaf.ResolutionClasses.sheafCohomologySource X)) K i) :
    nativeHomCochainEquiv K j (δ i j c) =
      (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (K.d i j) (nativeHomCochainEquiv K i c) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective c i (zero_add i)
  rw [Cochain.δ_fromSingleMk _ _ j j (zero_add j), nativeHomCochainEquiv_fromSingle,
    nativeHomCochainEquiv_fromSingle]
  exact SectionCoordinates.nativeSheafHomGlobalEquiv_naturality f (K.d i j)

def nativeHomComplexSectionsIso :
    ((singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) 0).obj (Chern.Sheaf.ResolutionClasses.sheafCohomologySource X)).HomComplex K ≅
      ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (nativeHomCochainEquiv K n).toAddCommGrpIso)
    (fun i j _ => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro c
      exact (nativeHomCochainEquiv_d K i j c).symm)

theorem nativeHomComplexSectionsIso_fromSingle (n : ℤ)
    (f : Chern.Sheaf.ResolutionClasses.sheafCohomologySource X ⟶ K.X n) :
    (nativeHomComplexSectionsIso K).hom.f n (Cochain.fromSingleMk f (zero_add n)) =
      SectionCoordinates.nativeSheafHomGlobalEquiv (K.X n) f :=
  nativeHomCochainEquiv_fromSingle K n f

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.HomComplexSections
