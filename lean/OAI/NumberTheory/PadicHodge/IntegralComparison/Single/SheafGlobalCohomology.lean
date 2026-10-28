import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.SupportedSurvivor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ZeroSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureFunctorNaturality

/-! # Sheaf Global Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.SheafGlobalCohomology

noncomputable section

/-! Global cohomology of the literal single sheaf agrees with the
original degree-zero ordered Čech cohomology of that sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Y : Scheme.{u}} (π : X ⟶ Y) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
  (M : X.Modules) (c : ℕ)

def iso :
    (((Supported.SectionsExcision.sections (D := AddCommGrpCat.{u}) ⊤).mapHomologicalComplex
      (.up ℕ)).obj (Closed.SupportedSurvivor.single M c)).homology c ≅
    (Trace.PureFunctorNaturality.cohomologyFunctor π U 0).obj M :=
  homologyMapIso
    ((singleMapHomologicalComplex (Supported.SectionsExcision.sections (D := AddCommGrpCat.{u}) ⊤)
      (.up ℕ) c).app (Closed.SupportedSurvivor.sheaf M)) c ≪≫
    singleObjHomologySelfIso (.up ℕ) c
      ((Supported.SectionsExcision.sections (D := AddCommGrpCat.{u}) ⊤).obj
        (Closed.SupportedSurvivor.sheaf M)) ≪≫
      (forget₂ (ModuleCat.{u} Γ(Y, ⊤)) AddCommGrpCat).mapIso (Cech.ZeroSections.iso π U hU M)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.SheafGlobalCohomology
