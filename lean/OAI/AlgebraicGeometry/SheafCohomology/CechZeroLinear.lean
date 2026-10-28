import OAI.AlgebraicGeometry.SheafCohomology.Cech.TopZero
import OAI.AlgebraicGeometry.SheafCohomology.CechScalars

/-! # Cech Zero Linear -/

namespace OAI.AlgebraicGeometry.SheafCohomology.CechZeroLinear

noncomputable section

/-! Global-function linearity of the degree-zero Čech injection. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u
namespace Projective

theorem globalSmulHom_apply_top {X : Scheme.{u}} (M : X.Modules)
    (r : Γ(X, ⊤)) (x : Γ(M, ⊤)) :
    (AffineH.Projective.globalSmulHom M r).app ⊤ x = r • x := by
  change X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op r • x = r • x
  rw [show (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op = 𝟙 _ from
    Subsingleton.elim _ _, X.presheaf.map_id]
  rfl

def globalSectionsCechHZeroLinear {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    letI := CechScalars.Projective.cechGlobalFunctionsModule M U 0
    Γ(M, ⊤) →ₗ[Γ(X, ⊤)] (CechScalars.Projective.moduleCechCohomologyFunctor U 0).obj M := by
  letI := CechScalars.Projective.cechGlobalFunctionsModule M U 0
  let f := Cech.TopZero.TopCat.Sheaf.cechTopSectionsToHZero U
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
  refine { toFun := f, map_add' := map_add f.hom, map_smul' := ?_ }
  intro r x
  have h := ConcreteCategory.congr_hom
    (Cech.TopZero.TopCat.Sheaf.cechTopSectionsToHZero_naturality U
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (AffineH.Projective.globalSmulHom M r))) x
  change (CechScalars.Projective.moduleCechCohomologyFunctor U 0).map (AffineH.Projective.globalSmulHom M r) (f x) =
    f ((AffineH.Projective.globalSmulHom M r).app ⊤ x) at h
  rw [globalSmulHom_apply_top] at h
  exact h.symm

theorem globalSectionsCechHZeroLinear_injective {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    Function.Injective (globalSectionsCechHZeroLinear M U) :=
  (AddCommGrpCat.mono_iff_injective _).mp
    (Cech.TopZero.TopCat.Sheaf.cechTopSectionsToHZero_mono U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) hU.iSup_eq_top)

end Projective

end

end OAI.AlgebraicGeometry.SheafCohomology.CechZeroLinear
