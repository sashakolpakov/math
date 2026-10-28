import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionTensorModelCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorCoefficientChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorComparisonNaturality

/-! # Tensor Coefficient Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorCoefficientChange

noncomputable section

/-! Changing the tensor coefficient algebra commutes with the actual geometric section comparison. A coefficient algebra isomorphism therefore transports the genuine model quasi-isomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

variable {R : Type u} [CommRing R]

theorem tensorCochainMap_naturality
    {B C : ModuleCat.{u} R} (α : B ⟶ C)
    {D E : CochainComplex (ModuleCat.{u} R) ℕ} (φ : D ⟶ E) :
    Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Tensor.CochainBicomplex.tensorCochainMap E α =
      Tensor.CochainBicomplex.tensorCochainMap D α ≫ Module.TensorFunctor.ModuleTensorFunctor.map C φ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro b x
  rfl

variable {X Y : Scheme.{u}} {B C : Type u} [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C]
variable (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (M : X.Modules)
variable (q : B →+* Γ(Y, ⊤)) (r : C →+* Γ(Y, ⊤))
variable (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f)
variable (hr : r.comp (algebraMap R C) = a.appTop.hom.comp f)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

theorem coefficientCechTensorPushforwardMap_coefficient_change
    (α : B →ₐ[R] C) (hα : r.comp α.toRingHom = q) :
    Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f M q hq U =
      Tensor.CochainBicomplex.tensorCochainMap (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f M U) (ModuleCat.ofHom α.toLinearMap) ≫
        Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f M r hr U := by
  let N : X.Modules := (Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)
  have h := TensorComparisonNaturality.CechTensorComparison.map_naturality B C f M N N U α.toLinearMap (𝟙 N)
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hq)
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a f M r hr)
    (fun V b x => (Module.TensorCoefficientChange.moduleSectionTensorComparisonApp_coefficient_change a f M q r hq hr α hα V b x).symm)
    (fun _ _ i b x => Module.SectionTensorNaturality.moduleSectionTensorComparisonApp_natural a f M q hq i.le b x)
    (fun _ _ i c x => Module.SectionTensorNaturality.moduleSectionTensorComparisonApp_natural a f M r hr i.le c x)
  let E := Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f N U
  let tq : Module.TensorFunctor.ModuleTensorFunctor.complex B (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f M U) ⟶ E :=
    Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f M q hq U
  have hid : (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor f U).map (𝟙 N) = 𝟙 E :=
    (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor f U).map_id N
  exact (Category.comp_id tq).symm.trans
    ((congrArg (fun v : E ⟶ E => tq ≫ v) hid).symm.trans h)

theorem coefficientCechModel_coefficient_change
    (α : B →ₐ[R] C) (hα : r.comp α.toRingHom = q)
    {D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f M U) :
    Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f M q hq U =
      Tensor.CochainBicomplex.tensorCochainMap D (ModuleCat.ofHom α.toLinearMap) ≫
        (Module.TensorFunctor.ModuleTensorFunctor.map C φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f M r hr U) := by
  let K := Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f M U
  let E := Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f
    ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) U
  let u : ModuleCat.of R B ⟶ ModuleCat.of R C := ModuleCat.ofHom α.toLinearMap
  let tq : Module.TensorFunctor.ModuleTensorFunctor.complex B K ⟶ E := Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f M q hq U
  let tr : Module.TensorFunctor.ModuleTensorFunctor.complex C K ⟶ E := Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f M r hr U
  have hc : tq = Tensor.CochainBicomplex.tensorCochainMap K u ≫ tr :=
    coefficientCechTensorPushforwardMap_coefficient_change a f M q r hq hr U α hα
  have hn : Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Tensor.CochainBicomplex.tensorCochainMap K u =
      Tensor.CochainBicomplex.tensorCochainMap D u ≫ Module.TensorFunctor.ModuleTensorFunctor.map C φ := tensorCochainMap_naturality u φ
  exact (congrArg (fun v : Module.TensorFunctor.ModuleTensorFunctor.complex B K ⟶ E => Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ v) hc).trans
    ((Category.assoc (Module.TensorFunctor.ModuleTensorFunctor.map B φ) (Tensor.CochainBicomplex.tensorCochainMap K u) tr).symm.trans
      ((congrArg (fun v : Module.TensorFunctor.ModuleTensorFunctor.complex B D ⟶ Module.TensorFunctor.ModuleTensorFunctor.complex C K => v ≫ tr) hn).trans
        (Category.assoc (Tensor.CochainBicomplex.tensorCochainMap D u) (Module.TensorFunctor.ModuleTensorFunctor.map C φ) tr)))

theorem coefficientCechModel_quasiIsoAt_of_coefficient_equiv
    (α : B ≃ₐ[R] C) (hα : r.comp α.toRingEquiv.toRingHom = q)
    {D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f M U) (n : ℕ)
    [hψ : QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map C φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f M r hr U) n] :
    QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f M q hq U) n := by
  let E := Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f
    ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) U
  let e : ModuleCat.of R B ≅ ModuleCat.of R C := α.toLinearEquiv.toModuleIso
  let eD : Module.TensorFunctor.ModuleTensorFunctor.complex B D ≅ Module.TensorFunctor.ModuleTensorFunctor.complex C D :=
    (Tensor.CochainBicomplex.tensorCochainFunctor D).mapIso e
  let ψ : Module.TensorFunctor.ModuleTensorFunctor.complex C D ⟶ E :=
    Module.TensorFunctor.ModuleTensorFunctor.map C φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f M r hr U
  have : QuasiIsoAt ψ n := hψ
  have hi : QuasiIsoAt (eD.hom ≫ ψ) n := quasiIsoAt_comp eD.hom ψ n
  have hm : Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a f M q hq U =
      eD.hom ≫ ψ := coefficientCechModel_coefficient_change a f M q r hq hr U α.toAlgHom hα φ
  exact (congrArg (fun v : Module.TensorFunctor.ModuleTensorFunctor.complex B D ⟶ E => QuasiIsoAt v n) hm).mpr hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorCoefficientChange
