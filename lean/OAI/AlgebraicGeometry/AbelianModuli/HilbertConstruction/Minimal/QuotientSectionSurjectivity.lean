import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.ModelSectionSurjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.FirstDifferentialIdeal

/-! # Quotient Section Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Killing the first differential of the actual minimal model supplies the generalized inverse required by the quotient section comparison. Restricting scalars preserves the actual differential identity. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u
section
variable {R B : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]

theorem Minimal.QuotientSectionSurjectivity.LocalSectionLifting.minimal_tensor_first_generalizedInverse
    {D : CochainComplex (ModuleCat.{u} R) ℕ} (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (D.sc' 0 1 2))
    (hQ : Q.complex.f.hom.baseChange B = 0) :
    ∃ r : (Module.TensorFunctor.ModuleTensorFunctor.complex B D).X 1 →ₗ[R] (Module.TensorFunctor.ModuleTensorFunctor.complex B D).X 0,
      ((Module.TensorFunctor.ModuleTensorFunctor.complex B D).d 0 1).hom.comp
        (r.comp ((Module.TensorFunctor.ModuleTensorFunctor.complex B D).d 0 1).hom) =
          ((Module.TensorFunctor.ModuleTensorFunctor.complex B D).d 0 1).hom := by
  obtain ⟨r, hr⟩ := Minimal.ModelSectionBaseChange.LocalSectionLifting.minimal_baseChange_first_generalizedInverse Q hQ
  let r' : (B ⊗[R] D.X 1) →ₗ[B] (B ⊗[R] D.X 0) := r
  refine ⟨r'.restrictScalars R, ?_⟩
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun hr x

theorem Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.firstDifferential_quotient_cochain_generalizedInverse
    {D : CochainComplex (ModuleCat.{u} R) ℕ} (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (D.sc' 0 1 2)) :
    ∃ r : (Module.TensorFunctor.ModuleTensorFunctor.complex (R ⧸ Q.firstDifferentialIdeal) D).X 1 →ₗ[R]
        (Module.TensorFunctor.ModuleTensorFunctor.complex (R ⧸ Q.firstDifferentialIdeal) D).X 0,
      ((Module.TensorFunctor.ModuleTensorFunctor.complex (R ⧸ Q.firstDifferentialIdeal) D).d 0 1).hom.comp
        (r.comp ((Module.TensorFunctor.ModuleTensorFunctor.complex (R ⧸ Q.firstDifferentialIdeal) D).d 0 1).hom) =
          ((Module.TensorFunctor.ModuleTensorFunctor.complex (R ⧸ Q.firstDifferentialIdeal) D).d 0 1).hom :=
  Minimal.QuotientSectionSurjectivity.LocalSectionLifting.minimal_tensor_first_generalizedInverse Q Q.firstDifferential_quotient_zero
end

variable {X Y Z : Scheme.{u}} {R B C : Type u} [CommRing R] [IsLocalRing R]
variable [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
variable (a : X ⟶ Y) (g : Y ⟶ Z) (f : R →+* Γ(Z, ⊤)) (M : Z.Modules)
variable (q : B →+* Γ(Y, ⊤)) (r : C →+* Γ(X, ⊤))
variable (hq : q.comp (algebraMap R B) = g.appTop.hom.comp f)
variable (hr : r.comp (algebraMap R C) = (a ≫ g).appTop.hom.comp f)
variable {ι : Type u} [LinearOrder ι] (U : ι → Z.Opens)

theorem Minimal.QuotientSectionSurjectivity.minimal_quotient_sectionTensor_surjective
    (h : Function.Surjective (algebraMap R B)) (hU : iSup U = ⊤)
    (hα : r.comp (algebraMap B C) = a.appTop.hom.comp q)
    {D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f M U)
    [QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap g f M q hq U) 0]
    [QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map C φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap (a ≫ g) f M r hr U) 0]
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (D.sc' 0 1 2))
    (hQ : Q.complex.f.hom.baseChange B = 0) :
    Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a (g.appTop.hom.comp f)
      ((Scheme.Modules.pullback g).obj M) r
      (Iterated.SectionTensorValues.sectionTensor_composite_coefficients a g f r hr) ⊤) := by
  obtain ⟨d, hd⟩ := Minimal.QuotientSectionSurjectivity.LocalSectionLifting.minimal_tensor_first_generalizedInverse Q hQ
  exact Quotient.ModelSectionSurjectivity.quotient_model_sectionTensor_surjective h a g f M q r hq hr U hU hα φ d hd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
