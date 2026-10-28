import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.GlobalModuleCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates

/-! # Global Coefficient Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.GlobalCoefficientFormula

noncomputable section

/-! The comparison with original algebraic Cech cochains retains every
literal regular coefficient on its tuple intersection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.TopCat.Sheaf

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

theorem cechGlobalModuleCoordinates_coefficient (n : ℕ) (c : Γ(TermModules.cechTermModule X U n, ⊤))
    (i : Fin (n + 1) → I) :
    SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv (TermModules.structureAbelianSheaf X).obj U n (GlobalModuleCoordinates.cechGlobalModuleCoordinates X U n c) i =
      ((TermModules.structureAbelianSheaf X).obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (ExtensionCoordinates.cechIntersection U n i))))).hom (ExtensionCoordinates.cechCoefficient U n ⊤ c i) := by
  let F := TermModules.structureAbelianSheaf X
  let C := SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm F U n
  let e := (CategoryTheory.Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
    AddCommGrpCat.{0} isTerminalTop).app C
  let p := AddEquiv.piCongrRight (fun j : Fin (n + 1) → I =>
    (F.obj.mapIso (eqToIso (congrArg op (top_inf_eq (ExtensionCoordinates.cechIntersection U n j))))).addCommGroupIsoToAddEquiv)
  change SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U n ((SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U n).symm
    (p (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U n ⊤ (e.hom (e.inv c))))) i = _
  erw [e.inv_hom_id_apply, AddEquiv.apply_symm_apply]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.GlobalCoefficientFormula
