import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModuleDifferential
import OAI.AlgebraicGeometry.SheafCohomology.Cech.GlobalSections

/-! # Global Module Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.GlobalModuleCoordinates

noncomputable section

/-! Global sections of the constructed Cech modules are the original
native algebraic Cech cochains, with their original differential. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.TopCat.Sheaf

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

def cechGlobalModuleCoordinates (n : ℕ) : Γ(TermModules.cechTermModule X U n, ⊤) ≃+
    ((CategoryTheory.cechComplexFunctor U).obj (TermModules.structureAbelianSheaf X).obj).X n :=
  (((CategoryTheory.Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
    AddCommGrpCat.{0} isTerminalTop).app (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm (TermModules.structureAbelianSheaf X) U n)).symm ≪≫
      SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsXIso (TermModules.structureAbelianSheaf X) U n).addCommGroupIsoToAddEquiv

theorem cechGlobalModuleCoordinates_differential (n : ℕ) (c : Γ(TermModules.cechTermModule X U n, ⊤)) :
    cechGlobalModuleCoordinates X U (n + 1) ((ModuleDifferential.cechModuleDifferential X U n).app ⊤ c) =
      ((CategoryTheory.cechComplexFunctor U).obj (TermModules.structureAbelianSheaf X).obj).d n (n + 1)
        (cechGlobalModuleCoordinates X U n c) := by
  let F := TermModules.structureAbelianSheaf X
  let e := CategoryTheory.Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
    AddCommGrpCat.{0} isTerminalTop
  have hn := ConcreteCategory.congr_hom (e.inv.naturality (SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechDifferential F U n)) c
  have hd := ConcreteCategory.congr_hom ((SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsComplexIso F U).hom.comm n (n + 1))
    (e.inv.app (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm F U n) c)
  have ha := congrArg (fun f => f.hom.app (op (⊤ : X.Opens)) c)
    (ModuleDifferential.cechModuleDifferential_underlying X U n)
  change (ModuleDifferential.cechModuleDifferential X U n).app ⊤ c = (SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechDifferential F U n).hom.app (op ⊤) c at ha
  change (SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsXIso F U (n + 1)).hom
    (e.inv.app (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm F U (n + 1)) ((ModuleDifferential.cechModuleDifferential X U n).app ⊤ c)) = _
  rw [ha]
  change e.inv.app (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm F U (n + 1)) ((SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechDifferential F U n).hom.app (op ⊤) c) =
    (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechDifferential F U n) (e.inv.app (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm F U n) c) at hn
  rw [hn]
  change ((CategoryTheory.cechComplexFunctor U).obj F.obj).d n (n + 1)
      ((SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsXIso F U n).hom (e.inv.app (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm F U n) c)) =
    (SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsXIso F U (n + 1)).hom
      ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map ((SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechComplex F U).d n (n + 1))
        (e.inv.app (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm F U n) c)) at hd
  rw [SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechComplex_d] at hd
  exact hd.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.GlobalModuleCoordinates
