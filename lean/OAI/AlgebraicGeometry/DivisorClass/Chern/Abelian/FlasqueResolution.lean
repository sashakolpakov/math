import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.FlasqueComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.ResolutionHomology
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ResolutionHomotopy

/-! # Flasque Resolution -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.FlasqueResolution

noncomputable section

/-! Ordinary sheaf cohomology computed by an actual nonnegative flasque resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

def abelianSheafInjectiveResolution (F : TopCat.Sheaf AddCommGrpCat.{0} X) : InjectiveResolution F :=
  (HasInjectiveResolution.out (Z := F)).some

variable (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (he : ∀ n, K.ExactAt (n + 1))

include hK in
theorem abelianFlasqueResolutionLift_quasiIso :
    QuasiIso (((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he (abelianSheafInjectiveResolution (K.homology 0)))) := by
  have := HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift_quasiIso K he (abelianSheafInjectiveResolution (K.homology 0))
  exact FlasqueComparison.abelianFlasqueGlobalSections_quasiIso _ hK
    (fun n => FlasqueInjectives.injectiveAbelianSheaf_isFlasque
      ((abelianSheafInjectiveResolution (K.homology 0)).cocomplex.X n))

/-- The map is induced by the actual resolution lift and the native Ext cocycle construction. -/
def abelianFlasqueResolutionCohomologyEquiv (n : ℕ) :
    (CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex K).homology (n + 1) ≃+ CategoryTheory.Sheaf.H (K.homology 0) (n + 1) := by
  have := abelianFlasqueResolutionLift_quasiIso K hK he
  exact (isoOfQuasiIsoAt
    (((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he (abelianSheafInjectiveResolution (K.homology 0))))
        (n + 1)).addCommGroupIsoToAddEquiv.trans
    (Chern.Sheaf.ResolutionHomology.sheafResolutionHomologyEquiv (abelianSheafInjectiveResolution (K.homology 0)) n)

/-- Identify degree zero with the original coefficient sheaf through its supplied actual isomorphism. -/
def abelianFlasqueResolutionCohomologyEquivOfIso (n : ℕ)
    {F : TopCat.Sheaf AddCommGrpCat.{0} X} (e : F ≅ K.homology 0) :
    (CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex K).homology (n + 1) ≃+ CategoryTheory.Sheaf.H F (n + 1) :=
  (abelianFlasqueResolutionCohomologyEquiv K hK he n).trans
    (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).mapIso e).addCommGroupIsoToAddEquiv.symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.FlasqueResolution
