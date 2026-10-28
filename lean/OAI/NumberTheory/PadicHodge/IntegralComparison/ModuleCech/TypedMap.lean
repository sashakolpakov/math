import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget

/-! # Typed Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TypedMap

noncomputable section

/-! An explicitly typed map of the original base-linear Čech complexes. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) {ι : Type u} (U : ι → X.Opens)
  {M N : X.Modules} (a : M ⟶ N)
def map : AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U ⟶ AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π N U := by
  change (cechComplexFunctor U).obj (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M) ⟶
    (cechComplexFunctor U).obj (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π N)
  exact (cechComplexFunctor U).map ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TypedMap
