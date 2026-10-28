import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueResolutionComparison
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Flasque Derived Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions

noncomputable section

/-! Actual flasque section cohomology computes the native right derived section functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}}

def rationalSheafInjectiveResolution (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) : InjectiveResolution F :=
  (HasInjectiveResolution.out (Z := F)).some

variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (he : ∀ n, K.ExactAt (n+1))

def flasqueResolutionDerivedCohomologyIso (U : Opens X) (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U K).homology n ≅
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).rightDerived n).obj (K.homology 0) :=
  FlasqueResolutionComparison.Constructions.flasqueResolutionSectionCohomologyIso K hK he (rationalSheafInjectiveResolution (K.homology 0)) U n ≪≫
    ((rationalSheafInjectiveResolution (K.homology 0)).isoRightDerivedObj (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U) n).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions
