import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroCycleCoordinates

/-! # Base Cech Global Sections -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.BaseCechGlobalSections.Construction

noncomputable section

/-! Literal global sections and ordered Cech zero-cycles agree linearly over the actual base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)

/-- The section-to-zero-cycle comparison retains the actual base scalar action. -/
def orderedBaseGlobalSectionsLinearEquiv :
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤) ≃ₗ[Γ(S, ⊤)]
      ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom.ker :=
  { SheafCohomology.Projective.BaseZeroCyclesSections.orderedBaseTopSectionsZeroCyclesAddEquiv π M U hU with
    map_smul' r x := by
      apply Subtype.ext
      apply (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechObjectIsoPi π M U 0).toLinearEquiv.injective
      funext a
      change (Pi.π (fun b : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 b.val) a)
        (SheafCohomology.Projective.BaseZeroCyclesSections.orderedBaseTopSectionsZeroCyclesAddEquiv π M U hU (r • x)).val =
        (Pi.π (fun b : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 b.val) a)
          (r • (SheafCohomology.Projective.BaseZeroCyclesSections.orderedBaseTopSectionsZeroCyclesAddEquiv π M U hU x).val)
      exact (SheafCohomology.Projective.BaseZeroCycleCoordinates.orderedBaseTopSectionsZeroCyclesAddEquiv_coordinate
        π M U hU (r • x) a).trans
        ((((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map (homOfLE (show
          (∏ᶜ fun k : Fin 1 => U (a.val k)) ≤ ⊤ from le_top)).op).hom.map_smul r x).trans
          ((congrArg (fun z : SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 a.val => r • z)
            (SheafCohomology.Projective.BaseZeroCycleCoordinates.orderedBaseTopSectionsZeroCyclesAddEquiv_coordinate
              π M U hU x a).symm).trans
            ((Pi.π (fun b : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 b.val) a).hom.map_smul
              r (SheafCohomology.Projective.BaseZeroCyclesSections.orderedBaseTopSectionsZeroCyclesAddEquiv π M U hU x).val).symm)) }

theorem orderedBaseGlobalSectionsLinearEquiv_coordinate
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤)) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    (Pi.π (fun b : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 b.val) a)
        (orderedBaseGlobalSectionsLinearEquiv π M U hU s).val =
      M.presheaf.map (homOfLE (show (∏ᶜ fun k : Fin 1 => U (a.val k)) ≤ ⊤ from le_top)).op s :=
  SheafCohomology.Projective.BaseZeroCycleCoordinates.orderedBaseTopSectionsZeroCyclesAddEquiv_coordinate π M U hU s a

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.BaseCechGlobalSections.Construction
