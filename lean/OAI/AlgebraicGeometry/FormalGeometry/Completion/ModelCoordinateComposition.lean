import OAI.AlgebraicGeometry.FormalGeometry.Completion.ModelTensorCoordinates
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SectionScalarComposition
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarKernelTransition

/-! # Model Coordinate Composition -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ModelCoordinateComposition

noncomputable section

/-! The local coordinates of the finite model comparison commute with
successive geometric base changes, for every tensor and in every degree. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings TensorProduct

namespace Construction

universe u

theorem appTop_comp_ringHom {S T T' : Scheme.{u}} (g : T ⟶ S) (t : T' ⟶ T) :
    t.appTop.hom.comp g.appTop.hom = (t ≫ g).appTop.hom := by
  rw [Scheme.Hom.comp_appTop]
  rfl

variable {X Y Z S T T' : Scheme.{u}}
  (f : Y ⟶ X) (j : Z ⟶ Y) (π : X ⟶ S) (ρ : Y ⟶ T) (τ : Z ⟶ T')
  (g : T ⟶ S) (t : T' ⟶ T) (h : f ≫ π = ρ ≫ g) (hj : j ≫ ρ = τ ≫ t)
  (M : X.Modules) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
  (φ : C ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)

include h hj in
theorem composedBaseChangeSquare : (j ≫ f) ≫ π = τ ≫ (t ≫ g) := by
  rw [Category.assoc, h, ← Category.assoc, hj, Category.assoc]

def modelCoordinatePullback (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) :
    (ModuleCat.extendScalars g.appTop.hom).obj (C.X q) →+
      SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor τ ((Scheme.Modules.pullback (j ≫ f)).obj M)
        (fun k => (j ≫ f) ⁻¹ᵁ U k) q i.1 :=
  (SectionScalarComposition.Construction.basePullbackCompSections f j τ M (∏ᶜ fun k => (j ≫ f) ⁻¹ᵁ U (i.1 k))).toAddMonoidHom.comp
    ((BaseSectionPullbackRestriction.Construction.restrictedBaseSectionPullback j ρ τ t hj ((Scheme.Modules.pullback f).obj M)
      (∏ᶜ fun k => f ⁻¹ᵁ U (i.1 k)) (∏ᶜ fun k => (j ≫ f) ⁻¹ᵁ U (i.1 k))
      (le_of_eq ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection j) (fun k => f ⁻¹ᵁ U k) q i.1).symm)).hom.toAddMonoidHom.comp
        ((Pi.π (fun k : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
          SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun k => f ⁻¹ᵁ U k) q k.1) i).hom.toAddMonoidHom.comp
          ((Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ).f q).hom.toAddMonoidHom))

theorem modelCoordinatePullback_tmul (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q)
    (a : Γ(T, ⊤)) (c : C.X q) :
    modelCoordinatePullback f j π ρ τ g t h hj M U φ q i (a ⊗ₜ[Γ(S, ⊤),g.appTop.hom] c) =
      Pi.π (fun k : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
        SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor τ ((Scheme.Modules.pullback (j ≫ f)).obj M)
          (fun k => (j ≫ f) ⁻¹ᵁ U k) q k.1) i
        ((Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (j ≫ f) π τ (t ≫ g)
          (composedBaseChangeSquare f j π ρ τ g t h hj) M U φ).f q
            (t.appTop a ⊗ₜ[Γ(S, ⊤),(t ≫ g).appTop.hom] c)) := by
  change SectionScalarComposition.Construction.basePullbackCompSections f j τ M (∏ᶜ fun k => (j ≫ f) ⁻¹ᵁ U (i.1 k))
    (BaseSectionPullbackRestriction.Construction.restrictedBaseSectionPullback j ρ τ t hj ((Scheme.Modules.pullback f).obj M)
      (∏ᶜ fun k => f ⁻¹ᵁ U (i.1 k)) (∏ᶜ fun k => (j ≫ f) ⁻¹ᵁ U (i.1 k))
      (le_of_eq ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection j) (fun k => f ⁻¹ᵁ U k) q i.1).symm)
      (Pi.π (fun k : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
        SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun k => f ⁻¹ᵁ U k) q k.1) i
        ((Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ).f q
        (a ⊗ₜ[Γ(S, ⊤),g.appTop.hom] c)))) = _
  rw [ModelTensorCoordinates.Construction.modelTensor_coordinate, ModelTensorCoordinates.Construction.modelTensor_coordinate, BaseSectionPullbackRestriction.Construction.restrictedBaseSectionPullback_apply]
  exact SectionScalarComposition.Construction.restrictedSection_smul_comp f j ρ τ t hj M _ _ _ _ _ a _

theorem modelCoordinatePullback_eq (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q)
    (x : (ModuleCat.extendScalars g.appTop.hom).obj (C.X q)) :
    modelCoordinatePullback f j π ρ τ g t h hj M U φ q i x =
      Pi.π (fun k : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
        SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor τ ((Scheme.Modules.pullback (j ≫ f)).obj M)
          (fun k => (j ≫ f) ⁻¹ᵁ U k) q k.1) i
        ((Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (j ≫ f) π τ (t ≫ g)
          (composedBaseChangeSquare f j π ρ τ g t h hj) M U φ).f q
            (ScalarKernelTransition.Construction.scalarCochainTransitionAtOfEq g.appTop.hom t.appTop.hom (t ≫ g).appTop.hom
              (appTop_comp_ringHom g t) C q x)) := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul a c =>
      rw [ScalarKernelTransition.Construction.scalarCochainTransitionAtOfEq_tmul]
      exact modelCoordinatePullback_tmul f j π ρ τ g t h hj M U φ q i a c
  | add x y hx hy => simp only [map_add, hx, hy]

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ModelCoordinateComposition
