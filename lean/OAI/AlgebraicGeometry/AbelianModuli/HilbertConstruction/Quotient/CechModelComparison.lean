import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.CechTensorPushforward
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.TensorScalarChange

/-! # Cech Model Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.CechModelComparison

noncomputable section

/-! Quotient scalar cancellation identifies the actual twice-tensored model comparison with the direct comparison. In particular, its quasi-isomorphism is deduced from the direct geometric comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u
variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
variable (h : Function.Surjective (algebraMap R B))

def quotientDoubleTensorCochainIso (D : CochainComplex (ModuleCat.{u} R) ℕ) :
    Module.TensorFunctor.ModuleTensorFunctor.complex C (Module.TensorFunctor.ModuleTensorFunctor.complex B D) ≅ Module.TensorFunctor.ModuleTensorFunctor.complex C D :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((TensorScalarChange.quotientDoubleTensorEquiv (C := C) h (D.X n)).restrictScalars R).toModuleIso)
    (by
      intro i j _
      apply ModuleCat.hom_ext
      exact TensorProduct.ext_threefold' (fun _ _ _ => rfl))

theorem quotientDoubleTensorCochainIso_hom (D : CochainComplex (ModuleCat.{u} R) ℕ) :
    (quotientDoubleTensorCochainIso (C := C) h D).hom =
      DoubleTensorCochainMap.doubleTensorCochainMap (Iterated.CechTensorPushforward.sectionTensorCoefficientProduct (IsScalarTower.toAlgHom R B C)) D := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold'
  intro c b x
  change (b • c) ⊗ₜ[R] x = (c * algebraMap B C b) ⊗ₜ[R] x
  rw [Algebra.smul_def, mul_comm]

variable {X Y Z : Scheme.{u}}
variable (a : X ⟶ Y) (g : Y ⟶ Z) (f : R →+* Γ(Z, ⊤)) (M : Z.Modules)
variable (q : B →+* Γ(Y, ⊤)) (r : C →+* Γ(X, ⊤))
variable (hq : q.comp (algebraMap R B) = g.appTop.hom.comp f)
variable (hr : r.comp (algebraMap R C) = (a ≫ g).appTop.hom.comp f)
variable {ι : Type u} [LinearOrder ι] (U : ι → Z.Opens)

omit [Algebra B C] [IsScalarTower R B C] in
theorem coefficientCechModel_comp
    (α : B →ₐ[R] C) (hα : r.comp α.toRingHom = a.appTop.hom.comp q)
    {D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f M U) :
    Module.TensorFunctor.ModuleTensorFunctor.map C
        (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap g f M q hq U) ≫
        Iterated.CechTensorPushforward.refinementCechTensorMap a g f M r hr U =
      DoubleTensorCochainMap.doubleTensorCochainMap (Iterated.CechTensorPushforward.sectionTensorCoefficientProduct α) D ≫
        (Module.TensorFunctor.ModuleTensorFunctor.map C φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap (a ≫ g) f M r hr U) := by
  let F := (Module.TensorFunctor.ModuleTensorFunctor.tensor (R := R) C).mapHomologicalComplex (ComplexShape.up ℕ)
  change F.map (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap g f M q hq U) ≫ _ = _
  rw [F.map_comp, Category.assoc, Iterated.CechTensorPushforward.coefficientCechTensorPushforwardMap_comp a g f M q r hq hr U α hα]
  rw [← Category.assoc, ← DoubleTensorCochainMap.doubleTensorCochainMap_naturality, Category.assoc]

include h in
theorem quotientCechModel_quasiIsoAt
    (hα : r.comp (algebraMap B C) = a.appTop.hom.comp q)
    {D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f M U) (n : ℕ)
    [QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map C φ ≫
      Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap (a ≫ g) f M r hr U) n] :
    QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map C
      (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap g f M q hq U) ≫
        Iterated.CechTensorPushforward.refinementCechTensorMap a g f M r hr U) n := by
  rw [coefficientCechModel_comp a g f M q r hq hr U (IsScalarTower.toAlgHom R B C) hα φ,
    ← quotientDoubleTensorCochainIso_hom h D]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.CechModelComparison
