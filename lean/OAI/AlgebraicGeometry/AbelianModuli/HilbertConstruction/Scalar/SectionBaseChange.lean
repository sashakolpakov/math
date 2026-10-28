import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleTensorScalarAction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BundleSectionBaseChange

/-! # Section Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionBaseChange

noncomputable section

/-! The canonical section tensor comparison is linear over the changed base, and flat affine base change gives an equivalence with that full scalar action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct
universe u

variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (M : X.Modules)

local instance changedBaseTensorModule :
    Module Γ(Y, ⊤) (TensorProduct Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (.op ⊤))) := by
  change Module (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
    (TensorProduct Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (.op ⊤)))
  infer_instance

def baseChangeGlobalSectionsLinearMap :
    TensorProduct Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (.op ⊤)) →ₗ[Γ(Y, ⊤)]
        (Coefficient.ModulePresheaf.coefficientModulePresheaf b.appTop.hom ((Scheme.Modules.pullback a).obj M)).obj (.op ⊤) where
  toFun := fun z => (Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op ⊤) z
  map_add' z w := ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op ⊤)).hom.map_add z w
  map_smul' c z := by
    let : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    exact CompatibleTensorScalarAction.compatibleScalarTensorMap_left_action
      (Section.PresheafExtendedScalars.pushedCoefficientScalarComponent a f.appTop.hom ((Scheme.Modules.pullback a).obj M)
        b.appTop.hom ⊤)
      (Section.PresheafExtendedScalars.pushedCoefficientScalarComponent_coefficient a f.appTop.hom
        ((Scheme.Modules.pullback a).obj M) b.appTop.hom
        (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) ⊤)
      ((Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap a f.appTop.hom M).app (.op ⊤)).hom c z

def flat_lineBundleGlobalSectionsEquiv
    [IsAffine S] [IsAffine Y] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (L : Line.Bundles.LineBundle X) [Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)] :
    TensorProduct Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).obj (.op ⊤)) ≃ₗ[Γ(Y, ⊤)]
        (Coefficient.ModulePresheaf.coefficientModulePresheaf b.appTop.hom (L.pullback a).sheaf).obj (.op ⊤) :=
  LinearEquiv.ofBijective (baseChangeGlobalSectionsLinearMap H L.sheaf)
    (HilbertConstruction.Flat.BundleSectionBaseChange.flat_lineBundleTensorComparison_bijective H L)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionBaseChange
