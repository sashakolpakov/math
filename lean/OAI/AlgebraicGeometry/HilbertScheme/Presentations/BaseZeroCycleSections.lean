import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroCycleCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleProductElements

/-! # Base Zero Cycle Sections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseZeroCycleSections

noncomputable section

/-! Direct base-linear global-section coordinates in the degree-zero
Čech kernel, using only the literal section and restriction maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)

def baseSectionRestriction (V : X.Opens) :
    letI := Module.compHom Γ(M, ⊤) π.appTop.hom
    Γ(M, ⊤) →ₗ[Γ(S, ⊤)] (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op V) := by
  letI := Module.compHom Γ(M, ⊤) π.appTop.hom
  let a := (homOfLE (le_top : V ≤ (⊤ : X.Opens))).op
  refine { toFun := M.presheaf.map a, map_add' := map_add _, map_smul' := ?_ }
  intro r x
  change M.presheaf.map a (π.appTop r • x) =
    X.presheaf.map ((initialOpOfTerminal isTerminalTop).to (op V)) (π.appTop r) • M.presheaf.map a x
  rw [M.map_smul]
  congr 2

variable {ι : Type u} (U : ι → X.Opens)

def directBaseSectionsZeroCyclesLinearEquiv (hU : iSup U = ⊤) :
    letI := Module.compHom Γ(M, ⊤) π.appTop.hom
    Γ(M, ⊤) ≃ₗ[Γ(S, ⊤)] ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d 0 1).hom.ker := by
  letI := Module.compHom Γ(M, ⊤) π.appTop.hom
  let e := SheafCohomology.Projective.BaseZeroCyclesSections.baseTopSectionsZeroCyclesAddEquiv π M U hU
  refine { e with map_smul' := ?_ }
  intro r x
  apply Subtype.ext
  apply SheafCohomology.Projective.ModuleProductElements.moduleProductElement_ext (fun a : Fin 1 → ι => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 a)
  intro a
  let V := ∏ᶜ fun k : Fin 1 => U (a k)
  let p := Pi.π (fun b : Fin 1 → ι => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 b) a
  change p (e (r • x)).val = p (r • (e x).val)
  calc
    p (e (r • x)).val = baseSectionRestriction π M V (r • x) :=
      SheafCohomology.Projective.BaseZeroCycleCoordinates.baseTopSectionsZeroCyclesAddEquiv_coordinate π M U hU (r • x) a
    _ = r • baseSectionRestriction π M V x := (baseSectionRestriction π M V).map_smul r x
    _ = r • p (e x).val := congrArg (fun y => r • y)
      (SheafCohomology.Projective.BaseZeroCycleCoordinates.baseTopSectionsZeroCyclesAddEquiv_coordinate π M U hU x a).symm
    _ = p (r • (e x).val) := (p.hom.map_smul r (e x).val).symm

def directOrderedSectionsZeroCyclesLinearEquiv [LinearOrder ι] (hU : iSup U = ⊤) :
    letI := Module.compHom Γ(M, ⊤) π.appTop.hom
    Γ(M, ⊤) ≃ₗ[Γ(S, ⊤)] ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom.ker := by
  letI := Module.compHom Γ(M, ⊤) π.appTop.hom
  exact (directBaseSectionsZeroCyclesLinearEquiv π M U hU).trans (SheafCohomology.Projective.OrderedBaseZeroCycles.Scheme.Modules.baseCechOrderedZeroCyclesEquiv π M U)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseZeroCycleSections
