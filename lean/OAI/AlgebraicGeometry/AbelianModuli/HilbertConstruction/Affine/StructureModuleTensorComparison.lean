import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.ModuleTensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.ModuleTensorComparison

/-! # Structure Module Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StructureModuleTensorComparison

noncomputable section

/-! For the structure module, the tensor comparison is an isomorphism on every affine open after affine base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry

universe u

theorem affineOpen_structureModuleTensorComparison_isIso
    {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H (Line.Bundles.structureModule X)).app (.op U)) := by
  let N := (AlgebraSectionModules.commAlgToModules Γ(S, ⊤)).obj (TensorSectionComparison.morphismGlobalAlgebra g)
  let α := (Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H (Line.Bundles.structureModule X)).app (.op U)
  let β := (TensorSectionComparison.baseChangeTensorSectionComparison H).app (.op U)
  let e := (Coefficient.StructureModuleComparison.coefficientStructureModuleComponent f.appTop.hom U).toModuleIso
  let d := (Structure.ModuleTensorTarget.baseChangedStructureModuleSectionsIso a f.appTop.hom).app (.op U)
  have h : α ≫ d.hom = (N ◁ e.hom) ≫ β := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro c r
    exact Structure.ModuleTensorComparison.structureModuleTensorComparison_tmul a f.appTop.hom (TensorSectionComparison.morphismGlobalAlgebra g) b.appTop.hom
      (TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) U c r
  have : IsIso β := TensorSectionComparison.affineOpen_tensorComparison_isIso H U hU
  have hi : IsIso ((N ◁ e.hom) ≫ β) := inferInstance
  have : IsIso (α ≫ d.hom) := (congrArg IsIso h).mpr hi
  exact (isIso_comp_right_iff α d.hom).mp this

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StructureModuleTensorComparison
