import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.CechModelComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardSections

/-! # Model Section Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.ModelSectionSurjectivity

noncomputable section

/-! A quotient model with a regular first differential gives the actual section tensor surjection for the next pullback. The second quasi-isomorphism is obtained from the original direct comparison, and pushforward sections are identified through their canonical coefficient-linear equivalence. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
section SectionComparison
variable {X Y Z : Scheme.{u}} {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
variable (a : X ⟶ Y) (g : Y ⟶ Z) (f : R →+* Γ(Z, ⊤)) (M : Z.Modules)
variable (r : C →+* Γ(X, ⊤))
variable (hr : r.comp (algebraMap R C) = (a ≫ g).appTop.hom.comp f)

theorem sectionTensor_surjective_of_refinement (U : Z.Opens)
    (h : Function.Surjective (Iterated.CechTensorPushforward.refinementSectionTensorComparisonApp a g f M r hr U)) :
    Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a (g.appTop.hom.comp f)
      ((Scheme.Modules.pullback g).obj M) r
      (Iterated.SectionTensorValues.sectionTensor_composite_coefficients a g f r hr) (g ⁻¹ᵁ U)) := by
  let N : Y.Modules := (Scheme.Modules.pullback g).obj M
  let K : X.Modules := (Scheme.Modules.pullback a).obj N
  let L : X.Modules := (Scheme.Modules.pullback (a ≫ g)).obj M
  let W := (a ≫ g) ⁻¹ᵁ U
  let e : K ≅ L := (Scheme.Modules.pullbackComp a g).app M
  let eR := ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ((a ≫ g).appTop.hom.comp f)).mapIso e).app (op W)
  let s := Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv g f N U
  let β := Module.SectionTensorComparison.moduleSectionTensorComparisonApp a (g.appTop.hom.comp f) N r
    (Iterated.SectionTensorValues.sectionTensor_composite_coefficients a g f r hr) (g ⁻¹ᵁ U)
  have he (z : C ⊗[R] ((Coefficient.ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward g).obj N)).obj (op U))) :
      e.hom.app W (β (s.toLinearMap.lTensor C z)) =
        Iterated.CechTensorPushforward.refinementSectionTensorComparisonApp a g f M r hr U z := by
    induction z with
    | add z w hz hw =>
        simp only [map_add]
        exact ((e.hom.app W).hom.map_add _ _).trans (congrArg₂ (· + ·) hz hw)
    | tmul c x => exact (Iterated.CechTensorPushforward.refinementSectionTensorComparisonApp_value a g f M r hr U c x).symm
  intro y
  let ey : (Coefficient.ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward (a ≫ g)).obj L)).obj (op U) :=
    e.hom.app W y
  obtain ⟨z, hz⟩ := h ey
  refine ⟨s.toLinearMap.lTensor C z, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso eR.hom).injective
  exact (he z).trans hz

theorem sectionTensor_top_surjective_of_refinement
    (h : Function.Surjective (Iterated.CechTensorPushforward.refinementSectionTensorComparisonApp a g f M r hr ⊤)) :
    Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a (g.appTop.hom.comp f)
      ((Scheme.Modules.pullback g).obj M) r
      (Iterated.SectionTensorValues.sectionTensor_composite_coefficients a g f r hr) ⊤) := by
  let P (V : Y.Opens) : Prop := Function.Surjective
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a (g.appTop.hom.comp f)
      ((Scheme.Modules.pullback g).obj M) r (Iterated.SectionTensorValues.sectionTensor_composite_coefficients a g f r hr) V)
  have hp : P (g ⁻¹ᵁ (⊤ : Z.Opens)) = P ⊤ :=
    congrArg P (Scheme.Hom.preimage_top g)
  exact hp.mp (sectionTensor_surjective_of_refinement a g f M r hr ⊤ h)
end SectionComparison

variable {X Y Z : Scheme.{u}} {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
variable (h : Function.Surjective (algebraMap R B))
variable (a : X ⟶ Y) (g : Y ⟶ Z) (f : R →+* Γ(Z, ⊤)) (M : Z.Modules)
variable (q : B →+* Γ(Y, ⊤)) (r : C →+* Γ(X, ⊤))
variable (hq : q.comp (algebraMap R B) = g.appTop.hom.comp f)
variable (hr : r.comp (algebraMap R C) = (a ≫ g).appTop.hom.comp f)
variable {ι : Type u} [LinearOrder ι] (U : ι → Z.Opens)

include h in
theorem quotient_model_sectionTensor_surjective
    (hU : iSup U = ⊤) (hα : r.comp (algebraMap B C) = a.appTop.hom.comp q)
    {D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f M U)
    [hφB : QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap g f M q hq U) 0]
    [QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map C φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap (a ≫ g) f M r hr U) 0]
    (d : (Module.TensorFunctor.ModuleTensorFunctor.complex B D).X 1 →ₗ[R] (Module.TensorFunctor.ModuleTensorFunctor.complex B D).X 0)
    (hd : ((Module.TensorFunctor.ModuleTensorFunctor.complex B D).d 0 1).hom.comp
      (d.comp ((Module.TensorFunctor.ModuleTensorFunctor.complex B D).d 0 1).hom) =
        ((Module.TensorFunctor.ModuleTensorFunctor.complex B D).d 0 1).hom) :
    Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a (g.appTop.hom.comp f)
      ((Scheme.Modules.pullback g).obj M) r
      (Iterated.SectionTensorValues.sectionTensor_composite_coefficients a g f r hr) ⊤) := by
  let N : Z.Modules := (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M)
  let P : Z.Modules := (Scheme.Modules.pushforward (a ≫ g)).obj ((Scheme.Modules.pullback (a ≫ g)).obj M)
  let φB := Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap g f M q hq U
  have hψ : QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map C φB ≫ Iterated.CechTensorPushforward.refinementCechTensorMap a g f M r hr U) 0 :=
    CechModelComparison.quotientCechModel_quasiIsoAt h a g f M q r hq hr U hα φ 0
  have hs : Function.Surjective (Iterated.CechTensorPushforward.refinementSectionTensorComparisonApp a g f M r hr ⊤) :=
    Cech.TensorSectionsSurjectivity.CechTensorComparison.sections_surjective_of_kernel_range (hφ := hφB) (hψ := hψ) C f N P U
      (Iterated.CechTensorPushforward.refinementSectionTensorComparisonApp a g f M r hr)
      (fun _ _ i c x => Iterated.CechTensorPushforward.refinementSectionTensorComparisonApp_natural a g f M r hr i.le c x)
      φB hU (Regular.DifferentialTensorKernel.tensor_kernel_range_of_generalizedInverse ((Module.TensorFunctor.ModuleTensorFunctor.complex B D).d 0 1).hom d hd C)
  exact sectionTensor_top_surjective_of_refinement a g f M r hr hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.ModelSectionSurjectivity
