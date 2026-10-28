import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechPresheafSheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange
import Mathlib.CategoryTheory.Sites.GlobalSections

/-! # Cech Section Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechSectionCoordinates.LargeZariskiCechSectionCoordinates

noncomputable section

/-! # Global sections of Čech sheaves are the actual intersection cochains -/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})

local instance coefficientLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

abbrev evaluation : MixedCech.Presheaf.MixedCechPresheaf.Presheaves R X ⥤ ModuleCat.{u + 1} R :=
  (CategoryTheory.evaluation _ _).obj (op (⊤ : X.Opens))

instance evaluation_limits : PreservesLimitsOfSize.{u, u} (LargeZariskiCechSectionCoordinates.evaluation R X) where
  preservesLimitsOfShape {_} _ := by unfold LargeZariskiCechSectionCoordinates.evaluation; infer_instance

def coefficientsIso (P : MixedCech.Presheaf.MixedCechPresheaf.Presheaves R X) :
    MixedCech.Presheaf.MixedCechPresheaf.intersectionCoefficients R X P ⋙ LargeZariskiCechSectionCoordinates.evaluation R X ≅ P :=
  NatIso.ofComponents (fun W => P.mapIso (eqToIso (congrArg op (top_inf_eq (a := W.unop))))) (by
    intro V W f
    change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
    rw [← P.map_comp, ← P.map_comp]
    congr 1)

variable {ι : Type u} (U : ι → X.Opens)

def presheafComplexIso (P : MixedCech.Presheaf.MixedCechPresheaf.Presheaves R X) :
    ((LargeZariskiCechSectionCoordinates.evaluation R X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((MixedCech.Functor.MixedCechFunctor.functor R X U).obj P) ≅ (cechComplexFunctor U).obj P :=
  Cech.CoefficientChange.CechCoefficientChange.complexIso (LargeZariskiCechSectionCoordinates.evaluation R X) (FormalCoproduct.mk ι U).cech
    (MixedCech.Presheaf.MixedCechPresheaf.intersectionCoefficients R X P) ≪≫
      (cechComplexFunctor U).mapIso (coefficientsIso R X P)

instance globalSections_additive :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).Additive :=
  Functor.additive_of_preserves_binary_products _

def sheafComplexIso (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)) :
    ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj ((MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U).obj F) ≅
        (cechComplexFunctor U).obj F.obj :=
  (NatIso.mapHomologicalComplex
    (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)
      (isTerminalTop : IsTerminal (⊤ : X.Opens))) (ComplexShape.up ℕ)).app
        ((MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U).obj F) ≪≫
    ((LargeZariskiCechSectionCoordinates.evaluation R X).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
      (CechPresheafSheaf.LargeZariskiCechPresheafSheaf.iso R X F U).symm ≪≫ presheafComplexIso R X U F.obj

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechSectionCoordinates.LargeZariskiCechSectionCoordinates
