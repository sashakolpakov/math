import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.ModuleTensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoverTensorComparison

/-! # Tensor Finite Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFiniteCover

noncomputable section

/-! Under flat coefficient extension, local invertibility of the module-section tensor comparison on a finite cover and its pairwise overlaps implies global invertibility. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry

universe u

theorem baseChangeModuleTensorComparison_isIso_of_finite_cover
    {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (M : X.Modules)
    [Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hlocal : ∀ i : Pairwise ι,
      IsIso ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op ((Pairwise.diagram U).obj i)))) :
    IsIso ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op ⊤)) := by
  have : Module.Flat Γ(S, ⊤) ((AlgebraSectionModules.commAlgToModules Γ(S, ⊤)).obj (Affine.TensorSectionComparison.morphismGlobalAlgebra g)) :=
    inferInstanceAs (Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g))
  have h := HilbertConstruction.Finite.CoverTensorComparison.finiteCoverTensorComparison_isIso
    (Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M)
    (Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom
      ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)))
    (Coefficient.ModulePresheaf.coefficientModulePresheaf_isSheaf _ _) (Coefficient.ModulePresheaf.coefficientModulePresheaf_isSheaf _ _)
    ((AlgebraSectionModules.commAlgToModules Γ(S, ⊤)).obj (Affine.TensorSectionComparison.morphismGlobalAlgebra g))
    (Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M) U hlocal
  exact (congrArg (fun V : X.Opens => IsIso ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op V))) hU).mp h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFiniteCover
