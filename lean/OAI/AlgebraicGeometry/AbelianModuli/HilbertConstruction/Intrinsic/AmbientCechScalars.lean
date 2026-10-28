import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientSectionScalars
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientCechNaturality

/-! # Ambient Cech Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientCechScalars

noncomputable section

/-! Multiplication by a coefficient commutes with the actual native ambient
Cech tensor map and the scalar endomorphism of its open-factor sheaf. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y P : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : P ⟶ X) (b : P ⟶ Y) (cX : R →+* Γ(X, ⊤)) (cY : R →+* Γ(Y, ⊤))
variable (hc : a.appTop.hom.comp cX = b.appTop.hom.comp cY) (M : X.Modules) (N : Y.Modules)

def nativeAmbientFactorScalar (U : Y.Opens) (r : R) :=
  Open.FactorSheafNaturality.IntrinsicCech.cechOpenFactorMap
    (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom (Global.ModuleScalars.globalModuleScalar
      (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N))
      ((a.appTop.hom.comp cX) r))) (b ⁻¹ᵁ U)

theorem nativeAmbientExternalComparisonPresheafMap_scalar (U : Y.Opens) (r : R) :
    AmbientCechNaturality.nativeAmbientExternalComparisonPresheafMap a b cX cY hc M N U ≫
      Functor.whiskerLeft (Opens.map a.base).op
        (nativeAmbientFactorScalar a b cX M N U r).hom =
    Functor.whiskerLeft (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M)
      (Functor.whiskerRight (Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
        (r • (LinearMap.id : ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U)) →ₗ[R]
          ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U))))) (Module.ProductForget.moduleForget R)) ≫
      AmbientCechNaturality.nativeAmbientExternalComparisonPresheafMap a b cX cY hc M N U := by
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro z
  let A := (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U)
  let B := (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj V
  change A ⊗[R] B at z
  have hz : ((r • (LinearMap.id : A →ₗ[R] A)).rTensor B) z = r • z := by
    induction z using TensorProduct.inductionOn with
    | tmul n m => simp only [LinearMap.rTensor_tmul, LinearMap.smul_apply,
        LinearMap.id_apply, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  change (nativeAmbientFactorScalar a b cX M N U r).hom.app (op (a ⁻¹ᵁ V.unop))
      ((AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b cX cY hc M N U).app V z) =
    (AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b cX cY hc M N U).app V
      (((r • (LinearMap.id : A →ₗ[R] A)).rTensor B) z)
  rw [hz]
  exact AmbientSectionScalars.nativeAmbientExternalSectionMap_scalar a b cX cY hc M N V.unop U r z

theorem nativeAmbientExternalCechTensorMap_scalar
    (U : Y.Opens) (r : R) {ι : Type u} [Finite ι] (V : ι → X.Opens) :
    AmbientCechTensor.nativeAmbientExternalCechTensorMap a b cX cY hc M N U V ≫
      (cechComplexFunctor V).map (Functor.whiskerLeft (Opens.map a.base).op
        (nativeAmbientFactorScalar a b cX M N U r).hom) =
    (NatTrans.mapHomologicalComplex
      (Functor.whiskerRight (Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
        (r • (LinearMap.id : ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U)) →ₗ[R]
          ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U))))) (Module.ProductForget.moduleForget R)) (.up ℕ)).app
      (CoefficientCechComplex.coefficientCechComplex cX M V) ≫
        AmbientCechTensor.nativeAmbientExternalCechTensorMap a b cX cY hc M N U V := by
  let A := (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U)
  let τ := Functor.whiskerRight (Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
    (r • (LinearMap.id : A →ₗ[R] A))) (Module.ProductForget.moduleForget R)
  let σ := AmbientCechNaturality.nativeAmbientExternalComparisonPresheafMap a b cX cY hc M N U
  let ρ := Functor.whiskerLeft (Opens.map a.base).op
    (nativeAmbientFactorScalar a b cX M N U r).hom
  let F : ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
    cechComplexFunctor V
  let E := HilbertConstruction.Finite.CechFunctorComparison.finiteCechFunctorIso (Module.TensorFunctor.ModuleTensorFunctor.tensor A ⋙ Module.ProductForget.moduleForget R)
    (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M) V
  let m := (NatTrans.mapHomologicalComplex τ (.up ℕ)).app (CoefficientCechComplex.coefficientCechComplex cX M V)
  let τ' := Functor.whiskerLeft (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M) τ
  have h : σ ≫ ρ = τ' ≫ σ :=
    nativeAmbientExternalComparisonPresheafMap_scalar a b cX cY hc M N U r
  change (E.hom ≫ F.map σ) ≫ F.map ρ = m ≫ (E.hom ≫ F.map σ)
  calc
    _ = E.hom ≫ F.map (σ ≫ ρ) :=
      (Category.assoc _ _ _).trans (congrArg (fun k => E.hom ≫ k) (F.map_comp σ ρ).symm)
    _ = E.hom ≫ F.map (τ' ≫ σ) := congrArg (fun k => E.hom ≫ F.map k) h
    _ = (E.hom ≫ F.map τ') ≫ F.map σ :=
      (congrArg (fun k => E.hom ≫ k) (F.map_comp τ' σ)).trans (Category.assoc _ _ _).symm
    _ = (m ≫ E.hom) ≫ F.map σ := congrArg (fun k => k ≫ F.map σ)
      (HilbertConstruction.Finite.CechFunctorNaturality.finiteCechFunctorIso_functor_naturality τ (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M) V).symm
    _ = _ := Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientCechScalars
