import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroCycleCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseGlobalRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleProductElements

/-! # Zero Cycles Linear Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ZeroCyclesLinearSections

noncomputable section

/-! Direct zero-cycle coordinates preserve the actual base-ring action. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} (U : ι → X.Opens)

def baseTopSectionsZeroCyclesLinearEquiv (hU : iSup U = ⊤) :
    letI := BaseZeroSections.baseGlobalSectionsModule π M
    Γ(M, ⊤) ≃ₗ[Γ(S, ⊤)] ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d 0 1).hom.ker := by
  letI := BaseZeroSections.baseGlobalSectionsModule π M
  let e := BaseZeroCyclesSections.baseTopSectionsZeroCyclesAddEquiv π M U hU
  refine { e with map_smul' := ?_ }
  intro r x
  apply Subtype.ext
  apply ModuleProductElements.moduleProductElement_ext (fun a : Fin 1 → ι => Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 a)
  intro a
  let V := ∏ᶜ fun k : Fin 1 => U (a k)
  let p := Pi.π (fun b : Fin 1 → ι => Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 b) a
  change p (e (r • x)).val = p (r • (e x).val)
  calc
    p (e (r • x)).val = BaseGlobalRestriction.baseGlobalRestriction π M V (r • x) :=
      BaseZeroCycleCoordinates.baseTopSectionsZeroCyclesAddEquiv_coordinate π M U hU (r • x) a
    _ = r • BaseGlobalRestriction.baseGlobalRestriction π M V x := (BaseGlobalRestriction.baseGlobalRestriction π M V).map_smul r x
    _ = r • p (e x).val := congrArg (fun y => r • y)
      (BaseZeroCycleCoordinates.baseTopSectionsZeroCyclesAddEquiv_coordinate π M U hU x a).symm
    _ = p (r • (e x).val) := (p.hom.map_smul r (e x).val).symm

def orderedBaseTopSectionsZeroCyclesLinearEquiv [LinearOrder ι] (hU : iSup U = ⊤) :
    letI := BaseZeroSections.baseGlobalSectionsModule π M
    Γ(M, ⊤) ≃ₗ[Γ(S, ⊤)] ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom.ker := by
  letI := BaseZeroSections.baseGlobalSectionsModule π M
  exact (baseTopSectionsZeroCyclesLinearEquiv π M U hU).trans
    (OrderedBaseZeroCycles.Scheme.Modules.baseCechOrderedZeroCyclesEquiv π M U)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ZeroCyclesLinearSections
