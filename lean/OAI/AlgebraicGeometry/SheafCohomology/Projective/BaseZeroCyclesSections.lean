import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseZeroCycles
import OAI.AlgebraicGeometry.SheafCohomology.Cech.TopZeroCycles

/-! # Base Zero Cycles Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroCyclesSections

noncomputable section

/-! Direct additive comparisons between literal sections and base-linear Čech zero cycles. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} (U : ι → X.Opens)

def baseCechZeroCyclesForgetEquiv :
    ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d 0 1).hom.ker ≃+
      Cech.TopZeroCycles.TopCat.Sheaf.nativeCechZeroCycles U (Module.ProjectiveAffine.ModuleSheaf.sheaf M) :=
  Cech.CochainZeroCycleMaps.Projective.addZeroCyclesEquivOfIso (BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π M U)

def baseTopSectionsZeroCyclesAddEquiv (hU : iSup U = ⊤) :
    Γ(M, ⊤) ≃+ ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d 0 1).hom.ker :=
  (Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsZeroCyclesEquiv U (Module.ProjectiveAffine.ModuleSheaf.sheaf M) hU).trans
    (baseCechZeroCyclesForgetEquiv π M U).symm

def orderedBaseTopSectionsZeroCyclesAddEquiv [LinearOrder ι] (hU : iSup U = ⊤) :
    Γ(M, ⊤) ≃+ ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom.ker :=
  (baseTopSectionsZeroCyclesAddEquiv π M U hU).trans
    (OrderedBaseZeroCycles.Scheme.Modules.baseCechOrderedZeroCyclesEquiv π M U).toAddEquiv

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroCyclesSections
