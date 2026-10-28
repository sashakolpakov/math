import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.PushforwardInjective
import OAI.AlgebraicGeometry.SheafCohomology.Cech.GlobalSectionsFunctor
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Whiskering

/-! # Pushforward Global Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PushforwardGlobalSections.Cech

noncomputable section

/-! Direct image and global sections commute on the actual sheaf complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

local instance (Z : TopCat.{u}) : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor Z).Additive :=
  (constantSheafΓAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).right_adjoint_additive

def pushforwardGlobalSectionsIso :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙ SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor Y ≅
      SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X :=
  Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
      (isTerminalTop (α := Opens Y))) ≪≫
    (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      (isTerminalTop (α := Opens X))).symm

def pushforwardGlobalSectionsComplexIso
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ) :
    ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor Y).mapHomologicalComplex (.up ℕ)).obj
      (((TopCat.Sheaf.pushforward AddCommGrpCat f).mapHomologicalComplex (.up ℕ)).obj K) ≅
    ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (pushforwardGlobalSectionsIso f).app (K.X n)) (fun i j _ =>
      ((pushforwardGlobalSectionsIso f).hom.naturality (K.d i j)).symm)

end

end OAI.AlgebraicGeometry.Comparison.Betti.PushforwardGlobalSections.Cech
