import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorSectionsSurjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionTensorNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.DifferentialTensorKernel

/-! # Section Tensor Model Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionTensorModelCriterion

noncomputable section

/-! The actual section tensor comparison over an original coefficient ring is surjective when its genuine Cech model and changed model compute degree zero and the first differential has a generalized inverse. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
variable {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Y, ⊤))
variable (hq : q.comp (algebraMap R B) = a.appTop.hom.comp c)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

def coefficientCechTensorPushforwardMap :
    Module.TensorFunctor.ModuleTensorFunctor.complex B (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U) ⟶
      Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) U :=
  OrderedCech.TensorComplex.CechTensorComparison.map B c M ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) U
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq)
    (fun _ _ i b x => Module.SectionTensorNaturality.moduleSectionTensorComparisonApp_natural a c M q hq i.le b x)

theorem coefficient_sectionTensor_surjective_of_regular_model
    (hU : iSup U = ⊤) {D : CochainComplex (ModuleCat.{u} R) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U)
    [hφ : QuasiIsoAt φ 0]
    [hψ : QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫
      coefficientCechTensorPushforwardMap a c M q hq U) 0]
    (r : D.X 1 →ₗ[R] D.X 0)
    (hr : (D.d 0 1).hom.comp (r.comp (D.d 0 1).hom) = (D.d 0 1).hom) :
    Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq ⊤) := by
  exact Cech.TensorSectionsSurjectivity.CechTensorComparison.sections_surjective_of_kernel_range
    (hφ := hφ) (hψ := hψ) B c M
    ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) U
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq)
    (fun _ _ i b x => Module.SectionTensorNaturality.moduleSectionTensorComparisonApp_natural a c M q hq i.le b x) φ hU
    (Regular.DifferentialTensorKernel.tensor_kernel_range_of_generalizedInverse (D.d 0 1).hom r hr B)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionTensorModelCriterion
