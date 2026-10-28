import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelOneTensor
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeFactors
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback

/-! # Model Tensor Coordinates -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ModelTensorCoordinates

noncomputable section

/-! The model comparison has explicit local coordinates on every pure
tensor, with arbitrary base scalar and actual restricted section pullback. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings

namespace Construction

universe u

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
  (h : f ≫ π = ρ ≫ g) (M : X.Modules)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
  (φ : C ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)

theorem modelTensor_coordinate (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) (a : Γ(T, ⊤)) (c : C.X q) :
    Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
      SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun k => f ⁻¹ᵁ U k) q j.1) i
      ((Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ).f q (a ⊗ₜ[Γ(S, ⊤),g.appTop.hom] c)) =
    @SMul.smul Γ(T, ⊤)
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun k => f ⁻¹ᵁ U k) q i.1) inferInstance a
      (Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map f M (∏ᶜ fun k => U (i.1 k)) (∏ᶜ fun k => f ⁻¹ᵁ U (i.1 k))
      (le_of_eq ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U q i.1).symm)
      (Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q j.1) i (φ.f q c))) := by
  let A := fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q j.1
  let B := fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
    SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun k => f ⁻¹ᵁ U k) q j.1
  have ht : (a ⊗ₜ[Γ(S, ⊤),g.appTop.hom] c : (ModuleCat.extendScalars g.appTop.hom).obj (C.X q)) =
      a • ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] c) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [ht, _root_.map_smul, _root_.map_smul, Quotients.FiniteDescent.ModelOneTensor.Construction.CechBaseChangeMap.model_one]
  have hc := ConcreteCategory.congr_hom
    (Quotients.FiniteDescent.CechBaseChangeComponents.Construction.CechBaseChangeMap.restricted_component_π f π ρ g h M U q i) (φ.f q c)
  change Pi.π B i ((Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap f π ρ g h M U).f q (φ.f q c)) =
    Quotients.FiniteDescent.CechBaseChangeComponents.Construction.CechBaseChangeMap.factorMap f π ρ g h M U q i (Pi.π A i (φ.f q c)) at hc
  rw [hc, Quotients.FiniteDescent.CechBaseChangeFactors.Construction.CechBaseChangeMap.factor_apply]
  rfl

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ModelTensorCoordinates
