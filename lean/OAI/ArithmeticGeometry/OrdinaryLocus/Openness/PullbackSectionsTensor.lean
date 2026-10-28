import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SemilinearScalarExtension

/-! # Pullback Sections Tensor -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackSectionsTensor.Construction

noncomputable section

/-! The canonical tensor comparison for global sections of a pulled-back scheme module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

def modulePullbackSectionsTensorMap :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Γ(X, ⊤) ⊗[Γ(Y, ⊤)] Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ((Scheme.Modules.pullback f).obj M, ⊤) := by
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  exact SemilinearScalarExtension.Construction.semilinearScalarExtension (PullbackModuleSections.Construction.modulePullbackGlobalSection f M)
    (PullbackModuleSections.Construction.modulePullbackGlobalSection_smul f M)

theorem modulePullbackSectionsTensorMap_tmul (a : Γ(X, ⊤)) (m : Γ(M, ⊤)) :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    modulePullbackSectionsTensorMap f M (a ⊗ₜ[Γ(Y, ⊤)] m) =
      a • PullbackModuleSections.Construction.modulePullbackGlobalSection f M m := rfl

def pullbackUnitGlobalSectionsIso :
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj
      ((Scheme.Modules.pullback f).obj (LineBundle.Construction.structureSheafModule Y)) ≅
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj (LineBundle.Construction.structureSheafModule X) :=
  (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso (LineBundle.Construction.pullbackStructureSheafIso f)

theorem modulePullbackSectionsTensorMap_unit (a : Γ(X, ⊤)) (r : Γ(Y, ⊤)) :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    (pullbackUnitGlobalSectionsIso f).hom
      (modulePullbackSectionsTensorMap f (LineBundle.Construction.structureSheafModule Y) (a ⊗ₜ[Γ(Y, ⊤)] r)) = a * f.appTop r := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  change (LineBundle.Construction.pullbackStructureSheafIso f).hom.app ⊤
    (a • PullbackModuleSections.Construction.modulePullbackGlobalSection f (LineBundle.Construction.structureSheafModule Y) r) = _
  rw [Scheme.Modules.Hom.app_smul, PullbackModuleSections.Construction.modulePullbackGlobalSection_unit]
  rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackSectionsTensor.Construction
