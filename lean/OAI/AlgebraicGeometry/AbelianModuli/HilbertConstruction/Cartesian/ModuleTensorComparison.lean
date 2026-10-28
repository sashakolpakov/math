import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionTensorNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorSectionComparison

/-! # Module Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.ModuleTensorComparison

noncomputable section

/-! An actual Cartesian square supplies the scalar compatibility and hence the canonical module-section tensor comparison. No affineness or flatness is needed to define this map. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry

universe u

variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (M : X.Modules)

def baseChangeModuleTensorComparison :
    Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M ⋙
        tensorLeft ((AlgebraSectionModules.commAlgToModules Γ(S, ⊤)).obj (Affine.TensorSectionComparison.morphismGlobalAlgebra g)) ⟶
      Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom
        ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) :=
  Module.SectionTensorNaturality.moduleSectionTensorComparison (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g) a f.appTop.hom M b.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H)

theorem baseChangeModuleTensorComparison_one (U : X.Opens)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (.op U)) :
    (baseChangeModuleTensorComparison H M).app (.op U) ((1 : Affine.TensorSectionComparison.morphismGlobalAlgebra g) ⊗ₜ[Γ(S, ⊤)] x) =
      (Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap a f.appTop.hom M).app (.op U) x :=
  Module.SectionTensorComparison.moduleSectionTensorComparisonApp_one (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g) a f.appTop.hom M b.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) U x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.ModuleTensorComparison
