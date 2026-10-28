import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechZeroGluing
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainZero
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange

/-! # Cech Model Sections -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections

noncomputable section

/-! Global sections after base change are the degree-zero differential kernel
of a universally valid finite Cech model. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechBaseChangeMap

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : f ≫ π = ρ ≫ g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)
variable [QuasiIsoAt (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ) 0]

def kernelSections :
    ((((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj D).d 0 1).hom.ker ≃ₗ[Γ(T, ⊤)]
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op ⊤) :=
  (CochainZero.Construction.CochainZeroCycles.kernelEquiv (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ)).trans
    (OrderedCechZeroGluing.Construction.OrderedCechZeroCoordinates.sectionsEquiv ρ ((Scheme.Modules.pullback f).obj M)
      (fun i => f ⁻¹ᵁ U i) (by rw [← f.preimage_iSup, hU]; rfl)).symm

theorem kernelSections_coordinate
    (x : ((((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj D).d 0 1).hom.ker) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map
      (homOfLE (show (∏ᶜ fun k => f ⁻¹ᵁ U (a.1 k)) ≤ ⊤ from le_top)).op
        (kernelSections f π ρ g h M U hU φ x) =
      Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 =>
        SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun i => f ⁻¹ᵁ U i) 0 j.1) a
          ((CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ).f 0 x.val) := by
  let e := OrderedCechZeroGluing.Construction.OrderedCechZeroCoordinates.sectionsEquiv ρ ((Scheme.Modules.pullback f).obj M)
    (fun i => f ⁻¹ᵁ U i) (by rw [← f.preimage_iSup, hU]; rfl)
  let k := CochainZero.Construction.CochainZeroCycles.kernelEquiv (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ)
  have he : e (kernelSections f π ρ g h M U hU φ x) = k x := e.apply_symm_apply (k x)
  have hc := OrderedCechZeroGluing.Construction.OrderedCechZeroCoordinates.sectionsEquiv_π ρ ((Scheme.Modules.pullback f).obj M)
    (fun i => f ⁻¹ᵁ U i) (by rw [← f.preimage_iSup, hU]; rfl)
    (kernelSections f π ρ g h M U hU φ x) a
  have hv := CochainZero.Construction.CochainZeroCycles.kernelEquiv_apply_val (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ) x
  have hp := congrArg (fun z => Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 =>
    SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun i => f ⁻¹ᵁ U i) 0 j.1) a z) hv
  exact hc.symm.trans ((congrArg (fun z => OrderedCechEq.Construction.OrderedCechZeroCoordinates.value ρ
    ((Scheme.Modules.pullback f).obj M) (fun i => f ⁻¹ᵁ U i) z a) he).trans hp)

end Construction.CechBaseChangeMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections
