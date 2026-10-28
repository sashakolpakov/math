import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorSectionsInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.CechTensorComparison

/-! # Section Tensor Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.SectionTensorInjection

noncomputable section

/-! Injectivity of the finite-model cycle inclusion after tensoring gives injectivity of the original Cartesian section tensor comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

theorem geometric_sectionTensor_injective_of_model_kernel_injective
    {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom M U)
    [hφ : QuasiIsoAt φ 0]
    [hψ : QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      CechTensorComparison.geometricCechTensorPushforwardMap H M U) 0]
    (h : Function.Injective ((D.d 0 1).hom.ker.subtype.lTensor (Affine.TensorSectionComparison.morphismGlobalAlgebra g))) :
    Function.Injective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (op ⊤)) := by
  exact Cech.TensorSectionsInjectivity.CechTensorComparison.sections_injective_of_kernel_tensor (hφ := hφ) (hψ := hψ)
    (Affine.TensorSectionComparison.morphismGlobalAlgebra g) f.appTop.hom M
    ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) U
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      a f.appTop.hom M b.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H))
    (fun _ _ i z x => Module.SectionTensorNaturality.moduleSectionTensorComparisonApp_natural
      (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g) a f.appTop.hom M b.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) i.le z x) φ hU h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.SectionTensorInjection
