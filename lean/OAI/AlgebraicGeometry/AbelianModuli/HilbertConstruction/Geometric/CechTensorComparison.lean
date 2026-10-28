import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.ModuleTensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardComplex

/-! # Cech Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.CechTensorComparison

noncomputable section

/-! The actual Cartesian section tensor map induces a Cech cochain map, with target the geometric inverse-image cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

def geometricCechTensorPushforwardMap :
    Module.TensorFunctor.ModuleTensorFunctor.complex (Affine.TensorSectionComparison.morphismGlobalAlgebra g) (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom M U) ⟶
      Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom
        ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) U :=
  OrderedCech.TensorComplex.CechTensorComparison.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) f.appTop.hom M
    ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) U
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      a f.appTop.hom M b.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H))
    (fun _ _ i z x => Module.SectionTensorNaturality.moduleSectionTensorComparisonApp_natural
      (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g) a f.appTop.hom M b.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) i.le z x)

def geometricCechTensorMap :
    Module.TensorFunctor.ModuleTensorFunctor.complex (Affine.TensorSectionComparison.morphismGlobalAlgebra g) (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom M U) ⟶
      Ordered.CoefficientCechComplex.orderedCoefficientCechComplex (a.appTop.hom.comp f.appTop.hom)
        ((Scheme.Modules.pullback a).obj M) (fun i => a ⁻¹ᵁ U i) :=
  geometricCechTensorPushforwardMap H M U ≫
    (OrderedCech.PushforwardComplex.orderedCoefficientCechComplexPushforwardIso a f.appTop.hom ((Scheme.Modules.pullback a).obj M) U).inv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.CechTensorComparison
