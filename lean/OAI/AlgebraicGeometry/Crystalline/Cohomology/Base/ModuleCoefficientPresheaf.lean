import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars
import OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Module Coefficient Presheaf -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ModuleCoefficientPresheaf.BaseModuleCoefficientPresheaf

noncomputable section

/-! # The original base-module sections retain their actual coefficient scalars -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

def coefficients : ModuleCat.{u} Γ(Spec (CommRingCat.of R), ⊤) ⥤ ModuleCat.{u} R :=
  ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

instance additive : (coefficients R).Additive := by
  dsimp only [coefficients]
  infer_instance

instance preservesLimits : PreservesLimitsOfSize.{u, u} (coefficients R) := by
  dsimp only [coefficients]
  infer_instance

instance preservesFiniteColimits : PreservesFiniteColimits (coefficients R) where
  preservesFiniteColimits J _ _ := by
    dsimp only [coefficients]
    infer_instance

instance preservesHomology : (coefficients R).PreservesHomology := by infer_instance

theorem constants (U : X.left.Opens) (r : R) :
    X.left.presheaf.map ((initialOpOfTerminal isTerminalTop).to (op U))
      (X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
        AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U r := by
  exact congrArg (fun f : op (⊤ : X.left.Opens) ⟶ op U =>
    X.left.presheaf.map f (X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)))
      (Subsingleton.elim _ _)

def sectionIso (M : X.left.Modules) (U : X.left.Opensᵒᵖ) :
    (coefficients R).obj ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf X.hom M).obj U) ≅
      ((NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.presheaves R X).obj M.val).obj U :=
  (AddEquiv.toLinearEquiv
    (M := ↑((coefficients R).obj ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf X.hom M).obj U)))
    (M₂ := ↑(((NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.presheaves R X).obj M.val).obj U))
    (by rfl) (by
      intro r x
      change @SMul.smul (X.left.ringCatSheaf.obj.obj U) (M.val.obj U) (M.val.obj U).isModule.toSMul
        (X.left.presheaf.map ((initialOpOfTerminal isTerminalTop).to U)
          (X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))) x =
        @SMul.smul (X.left.ringCatSheaf.obj.obj U) (M.val.obj U) (M.val.obj U).isModule.toSMul
          (AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U.unop r) x
      rw [constants])).toModuleIso

def iso (M : X.left.Modules) :
    SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf X.hom M ⋙ coefficients R ≅
      (NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.presheaves R X).obj M.val :=
  NatIso.ofComponents (sectionIso R X M) (by
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ModuleCoefficientPresheaf.BaseModuleCoefficientPresheaf
