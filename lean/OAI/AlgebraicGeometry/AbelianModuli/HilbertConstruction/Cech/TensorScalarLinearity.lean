import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.TensorLinearity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorCoefficientChange

/-! # Tensor Scalar Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorScalarLinearity

noncomputable section

/-! The actual Cech scalar-extension map intertwines every scalar in the
new coefficient algebra, including scalars outside the original ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

def coefficientAlgebraMultiplication (b : B) : B →ₗ[R] B where
  toFun c := b * c
  map_add' c d := mul_add b c d
  map_smul' r c := by
    change b * (r • c) = r • (b * c)
    rw [Algebra.smul_def, Algebra.smul_def]
    exact mul_left_comm b (algebraMap R B r) c

variable {X Y : Scheme.{u}}
    (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Y, ⊤))
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp c)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

theorem coefficientCechTensorPushforwardMap_scalar (b : B) :
    Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U ≫
        (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map
          ((Scheme.Modules.pushforward a).map (Global.ModuleScalars.globalModuleScalar ((Scheme.Modules.pullback a).obj M) (q b))) =
      Tensor.CochainBicomplex.tensorCochainMap (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U)
          (ModuleCat.ofHom (coefficientAlgebraMultiplication (R := R) b)) ≫
        Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U := by
  let N := (Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)
  let e := (Scheme.Modules.pushforward a).map (Global.ModuleScalars.globalModuleScalar ((Scheme.Modules.pullback a).obj M) (q b))
  exact TensorComparisonNaturality.CechTensorComparison.map_naturality B B c M N N U
    (coefficientAlgebraMultiplication b) e
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq)
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq)
    (fun V z x => by
      change Section.PresheafExtendedScalars.pushedCoefficientScalarComponent a c ((Scheme.Modules.pullback a).obj M) q V b
          (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq V (z ⊗ₜ[R] x)) =
        Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq V ((b * z) ⊗ₜ[R] x)
      simpa only [TensorProduct.smul_tmul', smul_eq_mul] using
        (Scalar.TensorLinearity.moduleSectionTensorComparisonApp_smul a c M q hq V b (z ⊗ₜ[R] x)).symm)
    (fun _ _ i z x => Module.SectionTensorNaturality.moduleSectionTensorComparisonApp_natural a c M q hq i.le z x)
    (fun _ _ i z x => Module.SectionTensorNaturality.moduleSectionTensorComparisonApp_natural a c M q hq i.le z x)

theorem coefficientCechModel_scalar (b : B)
    {C : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U) :
    (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U) ≫
        (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map
          ((Scheme.Modules.pushforward a).map (Global.ModuleScalars.globalModuleScalar ((Scheme.Modules.pullback a).obj M) (q b))) =
      Tensor.CochainBicomplex.tensorCochainMap C (ModuleCat.ofHom (coefficientAlgebraMultiplication (R := R) b)) ≫
        (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U) := by
  let K := Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U
  let E := Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c
    ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) U
  let t : Module.TensorFunctor.ModuleTensorFunctor.complex B K ⟶ E :=
    Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U
  let s : E ⟶ E := (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map
    ((Scheme.Modules.pushforward a).map (Global.ModuleScalars.globalModuleScalar ((Scheme.Modules.pullback a).obj M) (q b)))
  let u : ModuleCat.of R B ⟶ ModuleCat.of R B :=
    ModuleCat.ofHom (coefficientAlgebraMultiplication (R := R) b)
  let v : Module.TensorFunctor.ModuleTensorFunctor.complex B C ⟶ Module.TensorFunctor.ModuleTensorFunctor.complex B K :=
    Module.TensorFunctor.ModuleTensorFunctor.map B φ
  have hs : t ≫ s = Tensor.CochainBicomplex.tensorCochainMap K u ≫ t :=
    coefficientCechTensorPushforwardMap_scalar a c M q hq U b
  have hn : v ≫ Tensor.CochainBicomplex.tensorCochainMap K u = Tensor.CochainBicomplex.tensorCochainMap C u ≫ v :=
    TensorCoefficientChange.tensorCochainMap_naturality u φ
  change (v ≫ t) ≫ s = Tensor.CochainBicomplex.tensorCochainMap C u ≫ (v ≫ t)
  exact (Category.assoc v t s).trans
    ((congrArg (fun k => v ≫ k) hs).trans
      ((Category.assoc v (Tensor.CochainBicomplex.tensorCochainMap K u) t).symm.trans
        ((congrArg (fun k => k ≫ t) hn).trans
          (Category.assoc (Tensor.CochainBicomplex.tensorCochainMap C u) v t))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorScalarLinearity
