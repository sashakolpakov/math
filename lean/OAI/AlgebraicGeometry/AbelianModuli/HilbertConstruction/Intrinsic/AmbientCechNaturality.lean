import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientCechTensor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CechFunctorNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorHomologyNaturality

/-! # Ambient Cech Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientCechNaturality

noncomputable section

/-! Shrinking a parameter open gives a commuting square of the actual ambient Cech tensor maps. The target map is the native abelian-sheaf factor restriction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

variable {X Y P : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : P ⟶ X) (b : P ⟶ Y) (cX : R →+* Γ(X, ⊤)) (cY : R →+* Γ(Y, ⊤))
variable (hc : a.appTop.hom.comp cX = b.appTop.hom.comp cY) (M : X.Modules) (N : Y.Modules)

def nativeAmbientExternalComparisonPresheafMap (U : Y.Opens) :
    Coefficient.ModulePresheaf.coefficientModulePresheaf cX M ⋙
      (Module.TensorFunctor.ModuleTensorFunctor.tensor ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U)) ⋙ Module.ProductForget.moduleForget R) ⟶
    AmbientOpenFactorSections.ambientOpenFactorSectionPresheaf a (b ⁻¹ᵁ U)
      (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
        ((Scheme.Modules.pullback b).obj N))) :=
  (Functor.associator (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M)
    (Module.TensorFunctor.ModuleTensorFunctor.tensor ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U))) (Module.ProductForget.moduleForget R)).inv ≫
      AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b cX cY hc M N U

theorem nativeAmbientExternalComparisonPresheafMap_restrict
    {U U' : Y.Opens} (hU : U' ≤ U) :
    nativeAmbientExternalComparisonPresheafMap a b cX cY hc M N U ≫
      Functor.whiskerLeft (Opens.map a.base).op
        ((Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction
          (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
            ((Scheme.Modules.pullback b).obj N)))
          (leOfHom ((Opens.map b.base).map (homOfLE hU)))).hom) =
    Functor.whiskerLeft (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M)
      (Functor.whiskerRight (Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
        (((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).map (homOfLE hU).op).hom)) (Module.ProductForget.moduleForget R)) ≫
      nativeAmbientExternalComparisonPresheafMap a b cX cY hc M N U' := by
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro z
  let ρ := ((Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction
      (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
        ((Scheme.Modules.pullback b).obj N)))
      (leOfHom ((Opens.map b.base).map (homOfLE hU)))).hom.app (op (a ⁻¹ᵁ V.unop))).hom
  let σ := ((AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b cX cY hc M N U).app V).hom
  let σ' := ((AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b cX cY hc M N U').app V).hom
  let α := (((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).map (homOfLE hU).op).hom.rTensor
    ((Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj V)).toAddMonoidHom
  let l := ρ.comp σ
  let r := σ'.comp α
  change l z = r z
  induction z using TensorProduct.inductionOn with
  | tmul n m =>
      change ρ (σ (n ⊗ₜ[R] m)) = σ'
        ((((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).map (homOfLE hU).op).hom.rTensor
          ((Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj V)) (n ⊗ₜ[R] m))
      simpa only [LinearMap.rTensor_tmul] using
        AmbientExternalPresheafMap.nativeAmbientExternalSectionMap_parameter_restrict a b cX cY hc M N V.unop hU n m
  | add x y hx hy =>
      exact (l.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (r.map_add x y).symm)

theorem nativeAmbientExternalCechTensorMap_restrict
    {U U' : Y.Opens} (hU : U' ≤ U) {ι : Type u} [Finite ι] (V : ι → X.Opens) :
    AmbientCechTensor.nativeAmbientExternalCechTensorMap a b cX cY hc M N U V ≫
      (cechComplexFunctor V).map (Functor.whiskerLeft (Opens.map a.base).op
        ((Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction
          (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
            ((Scheme.Modules.pullback b).obj N)))
          (leOfHom ((Opens.map b.base).map (homOfLE hU)))).hom)) =
    (NatTrans.mapHomologicalComplex
      (Functor.whiskerRight (Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
        (((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).map (homOfLE hU).op).hom)) (Module.ProductForget.moduleForget R)) (.up ℕ)).app
      (CoefficientCechComplex.coefficientCechComplex cX M V) ≫
        AmbientCechTensor.nativeAmbientExternalCechTensorMap a b cX cY hc M N U' V := by
  let A := (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U)
  let A' := (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U')
  let τ := Functor.whiskerRight (Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
    (((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).map (homOfLE hU).op).hom)) (Module.ProductForget.moduleForget R)
  let σ := nativeAmbientExternalComparisonPresheafMap a b cX cY hc M N U
  let σ' := nativeAmbientExternalComparisonPresheafMap a b cX cY hc M N U'
  let ρ := Functor.whiskerLeft (Opens.map a.base).op
    ((Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction
      (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
        ((Scheme.Modules.pullback b).obj N)))
      (leOfHom ((Opens.map b.base).map (homOfLE hU)))).hom)
  have h : σ ≫ ρ = Functor.whiskerLeft (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M) τ ≫ σ' :=
    nativeAmbientExternalComparisonPresheafMap_restrict a b cX cY hc M N hU
  change ((HilbertConstruction.Finite.CechFunctorComparison.finiteCechFunctorIso (Module.TensorFunctor.ModuleTensorFunctor.tensor A ⋙ Module.ProductForget.moduleForget R)
      (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M) V).hom ≫ (cechComplexFunctor V).map σ) ≫
      (cechComplexFunctor V).map ρ =
    (NatTrans.mapHomologicalComplex τ (.up ℕ)).app (CoefficientCechComplex.coefficientCechComplex cX M V) ≫
      ((HilbertConstruction.Finite.CechFunctorComparison.finiteCechFunctorIso (Module.TensorFunctor.ModuleTensorFunctor.tensor A' ⋙ Module.ProductForget.moduleForget R)
        (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M) V).hom ≫ (cechComplexFunctor V).map σ')
  let F : (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
    cechComplexFunctor V
  let e := HilbertConstruction.Finite.CechFunctorComparison.finiteCechFunctorIso (Module.TensorFunctor.ModuleTensorFunctor.tensor A ⋙ Module.ProductForget.moduleForget R)
    (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M) V
  let e' := HilbertConstruction.Finite.CechFunctorComparison.finiteCechFunctorIso (Module.TensorFunctor.ModuleTensorFunctor.tensor A' ⋙ Module.ProductForget.moduleForget R)
    (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M) V
  let m := (NatTrans.mapHomologicalComplex τ (.up ℕ)).app (CoefficientCechComplex.coefficientCechComplex cX M V)
  let τ' := Functor.whiskerLeft (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M) τ
  have h₁ : (e.hom ≫ F.map σ) ≫ F.map ρ = e.hom ≫ F.map (σ ≫ ρ) :=
    (Category.assoc _ _ _).trans (congrArg (fun k => e.hom ≫ k) (F.map_comp σ ρ).symm)
  have h₂ : e.hom ≫ F.map (σ ≫ ρ) = e.hom ≫ F.map (τ' ≫ σ') :=
    congrArg (fun k => e.hom ≫ F.map k) h
  have h₃ : e.hom ≫ F.map (τ' ≫ σ') = (e.hom ≫ F.map τ') ≫ F.map σ' :=
    (congrArg (fun k => e.hom ≫ k) (F.map_comp τ' σ')).trans (Category.assoc _ _ _).symm
  have hn : e.hom ≫ F.map τ' = m ≫ e'.hom :=
    (HilbertConstruction.Finite.CechFunctorNaturality.finiteCechFunctorIso_functor_naturality τ (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M) V).symm
  exact h₁.trans (h₂.trans (h₃.trans
    ((congrArg (fun k => k ≫ F.map σ') hn).trans (Category.assoc _ _ _))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientCechNaturality
