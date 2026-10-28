import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorSectionsSurjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.CechTensorComparison

/-! # Section Tensor Model Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.SectionTensorModelCriterion

noncomputable section

/-! The finite-model kernel-range condition gives surjectivity of the original Cartesian section tensor comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

theorem geometric_sectionTensor_surjective_of_model_kernel_range
    {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom M U)
    [hφ : QuasiIsoAt φ 0]
    [hψ : QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      CechTensorComparison.geometricCechTensorPushforwardMap H M U) 0]
    (h : ((D.d 0 1).hom.lTensor (Affine.TensorSectionComparison.morphismGlobalAlgebra g)).ker ≤
      ((D.d 0 1).hom.ker.subtype.lTensor (Affine.TensorSectionComparison.morphismGlobalAlgebra g)).range) :
    Function.Surjective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (op ⊤)) := by
  exact Cech.TensorSectionsSurjectivity.CechTensorComparison.sections_surjective_of_kernel_range
    (hφ := hφ) (hψ := hψ)
    (Affine.TensorSectionComparison.morphismGlobalAlgebra g) f.appTop.hom M
    ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) U
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      a f.appTop.hom M b.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H))
    (fun _ _ i z x => Module.SectionTensorNaturality.moduleSectionTensorComparisonApp_natural
      (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g) a f.appTop.hom M b.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) i.le z x) φ hU h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.SectionTensorModelCriterion
