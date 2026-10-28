import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionCoefficientBasisChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SpecifiedSectionTensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionTensorModelCriterion

/-! # Pulled Section Completeness Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PulledSectionCompletenessCriterion

noncomputable section

/-! The actual pulled-back sections are complete exactly when their
specified cycles give a complete kernel basis in the scalar-extended Cech
model. This compares the section maps themselves, not only dimensions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Y, ⊤))
variable (hq : q.comp (algebraMap R B) = a.appTop.hom.comp c)
variable {κ : Type v} (s : κ → (Line.Bundles.structureModule X ⟶ M))

theorem sectionTensorCoefficients_value (x : B ⊗[R] (κ →₀ R)) :
    (show (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor q).obj ((Scheme.Modules.pullback a).obj M) from
      Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq ⊤
        ((Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s).lTensor B x)) =
      Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination q ((Scheme.Modules.pullback a).obj M)
        (fun i => Ample.LineBundles.pullbackSection a (s i)) (SectionCoefficientBasisChange.freeCoefficientBaseChangeEquiv x) := by
  have h := LinearMap.congr_fun (SectionCoefficientBasisChange.pulledSectionCoefficientMap_baseChange a c M q hq s) x
  have hb := congrFun (LinearMap.baseChange_eq_ltensor
    (A := B) (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s)) x
  exact (congrArg (Coefficient.SectionTensorScalarMap.coefficientSectionTensorScalarMap a c M q hq) hb.symm).trans h

theorem sectionTensorCoefficients_bijective_iff :
    Function.Bijective ((Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq ⊤).comp
      ((Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s).lTensor B)) ↔
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination q ((Scheme.Modules.pullback a).obj M)
      (fun i => Ample.LineBundles.pullbackSection a (s i))) := by
  let e := SectionCoefficientBasisChange.freeCoefficientBaseChangeEquiv (R := R) (B := B) (κ := κ)
  let v := Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination q ((Scheme.Modules.pullback a).obj M)
    (fun i => Ample.LineBundles.pullbackSection a (s i))
  have he : (fun x => Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq ⊤
      ((Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s).lTensor B x)) = fun x => v (e x) := by
    funext x
    exact sectionTensorCoefficients_value a c M q hq s x
  change Function.Bijective (fun x => Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq ⊤
    ((Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s).lTensor B x)) ↔ Function.Bijective v
  rw [he]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have h' : v (e (e.symm x)) = v (e (e.symm y)) := by
        simpa only [LinearEquiv.apply_symm_apply] using hxy
      exact e.symm.injective (h.injective h')
    · intro y
      obtain ⟨x, hx⟩ := h.surjective y
      exact ⟨e x, hx⟩
  · intro h
    exact h.comp e.bijective

theorem modelSectionCycles_complete_after_pullback_iff
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} R) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U) [QuasiIsoAt φ 0]
    [hψ : QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U) 0] :
    Function.Bijective (SpecifiedSectionTensorComparison.tensorSpecifiedSectionCycleComparison B c M U hU φ s) ↔
      Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination q ((Scheme.Modules.pullback a).obj M)
        (fun i => Ample.LineBundles.pullbackSection a (s i))) := by
  have : QuasiIsoAt (Cech.TensorModelSections.CechTensorComparison.modelMap B c M
      ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) U
      (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq)
      (fun _ _ i b x => Module.SectionTensorNaturality.moduleSectionTensorComparisonApp_natural a c M q hq i.le b x) φ) 0 := hψ
  exact (SpecifiedSectionTensorComparison.tensorSpecifiedSectionCycleComparison_bijective_iff B c M
    ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) U hU φ
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq)
    (fun _ _ i b x => Module.SectionTensorNaturality.moduleSectionTensorComparisonApp_natural a c M q hq i.le b x) s).trans
      (sectionTensorCoefficients_bijective_iff a c M q hq s)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PulledSectionCompletenessCriterion
