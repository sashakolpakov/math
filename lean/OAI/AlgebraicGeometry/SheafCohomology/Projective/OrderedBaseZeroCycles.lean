import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechAlternating
import OAI.AlgebraicGeometry.SheafCohomology.Cech.CochainZeroCycleMaps

/-! # Ordered Base Zero Cycles -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseZeroCycles

noncomputable section

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

/-! Restriction to ordered tuples identifies native and ordered Čech zero cycles directly. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u
namespace Scheme.Modules
variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

theorem baseCechToOrdered_zero_mono : Mono (OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF π M U 0) := by
  constructor
  intro Z f g h
  apply Pi.hom_ext (f := fun a : Fin 1 → ι => Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 a)
  intro a
  let b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 := ⟨a, Subsingleton.strictMono (α := Fin 1) a⟩
  have hb := congrArg (fun k => k ≫ Pi.π
    (fun c : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 c.val) b) h
  simpa only [Category.assoc, OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF_comp_π] using hb

def baseCechOrderedZeroCyclesEquiv :
    ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d 0 1).hom.ker ≃ₗ[Γ(S, ⊤)]
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom.ker :=
  LinearEquiv.ofBijective (Cech.CochainZeroCycleMaps.Projective.linearZeroCyclesMap (OrderedBaseCechComparison.Scheme.Modules.baseCechToOrdered π M U))
    (Cech.CochainZeroCycleMaps.Projective.linearZeroCyclesMap_bijective_of_split
      (OrderedBaseCechComparison.Scheme.Modules.baseCechToOrdered π M U) (OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternating π M U)
      (OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternating_comp_baseCechToOrdered π M U)
      ((ModuleCat.mono_iff_injective _).mp (baseCechToOrdered_zero_mono π M U)))

end Scheme.Modules

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseZeroCycles
