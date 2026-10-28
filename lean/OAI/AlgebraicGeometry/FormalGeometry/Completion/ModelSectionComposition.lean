import OAI.AlgebraicGeometry.FormalGeometry.Completion.ModelCoordinateComposition
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionComposition
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections

/-! # Model Section Composition -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ModelSectionComposition

noncomputable section

/-! The finite-model classification of actual global sections commutes
with successive geometric pullbacks, including arbitrary base scalars. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

namespace Construction

universe u

variable {X Y Z S T T' : Scheme.{u}}
  (f : Y ⟶ X) (j : Z ⟶ Y) (π : X ⟶ S) (ρ : Y ⟶ T) (τ : Z ⟶ T')
  (g : T ⟶ S) (t : T' ⟶ T) (h : f ≫ π = ρ ≫ g) (hj : j ≫ ρ = τ ≫ t)
  (M : X.Modules) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
  {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
  (φ : C ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)
  [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ) 0]
  [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (j ≫ f) π τ (t ≫ g)
    (ModelCoordinateComposition.Construction.composedBaseChangeSquare f j π ρ τ g t h hj) M U φ) 0]

theorem modelSection_composite_pullback
    (x : ((((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj C).d 0 1).hom.ker) :
    GlobalSectionComposition.Construction.globalSectionCompositePullback f j M (Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections f π ρ g h M U hU φ x) =
      Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections (j ≫ f) π τ (t ≫ g)
        (ModelCoordinateComposition.Construction.composedBaseChangeSquare f j π ρ τ g t h hj) M U hU φ
          (ScalarKernelTransition.Construction.scalarCochainKernelTransitionOfEq g.appTop.hom t.appTop.hom (t ≫ g).appTop.hom
            (ModelCoordinateComposition.Construction.appTop_comp_ringHom g t) C x) := by
  apply GlobalSectionComposition.Construction.globalSections_ext_cechCoordinates τ ((Scheme.Modules.pullback (j ≫ f)).obj M)
    (fun i => (j ≫ f) ⁻¹ᵁ U i) (by rw [← Scheme.Hom.preimage_iSup, hU]; rfl)
  intro i
  rw [GlobalSectionComposition.Construction.globalSectionCompositePullback_restriction f j M
    (∏ᶜ fun k => f ⁻¹ᵁ U (i.1 k)) (∏ᶜ fun k => (j ≫ f) ⁻¹ᵁ U (i.1 k))
    (le_of_eq ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection j) (fun k => f ⁻¹ᵁ U k) 0 i.1).symm)]
  rw [Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections_coordinate, Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections_coordinate,
    ScalarKernelTransition.Construction.scalarCochainKernelTransitionOfEq_val]
  have he := ModelCoordinateComposition.Construction.modelCoordinatePullback_eq f j π ρ τ g t h hj M U φ 0 i x.val
  change SectionScalarComposition.Construction.basePullbackCompSections f j τ M (∏ᶜ fun k => (j ≫ f) ⁻¹ᵁ U (i.1 k))
    (BaseSectionPullbackRestriction.Construction.restrictedBaseSectionPullback j ρ τ t hj ((Scheme.Modules.pullback f).obj M)
      (∏ᶜ fun k => f ⁻¹ᵁ U (i.1 k)) (∏ᶜ fun k => (j ≫ f) ⁻¹ᵁ U (i.1 k))
      (le_of_eq ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection j) (fun k => f ⁻¹ᵁ U k) 0 i.1).symm)
      (Pi.π (fun k : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 =>
        SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun k => f ⁻¹ᵁ U k) 0 k.1) i
        ((Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ).f 0 x.val))) = _ at he
  rw [BaseSectionPullbackRestriction.Construction.restrictedBaseSectionPullback_apply, SectionScalarComposition.Construction.basePullbackCompSections_apply] at he
  exact he

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ModelSectionComposition
