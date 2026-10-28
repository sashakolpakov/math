import OAI.AlgebraicGeometry.DivisorClass.Chern.ModuleGlobalSectionsForget
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality
import OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition
import OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology

/-! # Cochain Forget -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.CochainForget

noncomputable section

/-! Forgetting complex scalars preserves the original actual cocycle class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (K : CochainComplex (ModuleCat.{0} ℂ) ℕ) (n : ℕ)

def complexForgetCycleClass (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (n + 1)) :
    ((SheafForget.complexModuleForget.mapHomologicalComplex (.up ℕ)).obj K).homology (n + 1) :=
  ((SheafForget.complexModuleForget.mapHomologicalComplex (.up ℕ)).obj K).homologyπ (n + 1)
    (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n _ c.val ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K (n + 1) c.val).mp c.property))

theorem complexForgetCycleClass_map (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (n + 1)) :
    (ModuleGlobalSectionsForget.complexForgetHomologyIso K (n + 1)).hom (complexForgetCycleClass K n c) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K (n + 1) c := by
  let L := (SheafForget.complexModuleForget.mapHomologicalComplex (.up ℕ)).obj K
  let S := K.sc (n + 1)
  let z := SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n L c.val ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K (n + 1) c.val).mp c.property)
  have hz : (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactCyclesIso S SheafForget.complexModuleForget).hom z = (K.sc (n + 1)).moduleCatCyclesIso.inv c := by
    apply (ModuleCat.mono_iff_injective (K.iCycles (n + 1))).mp inferInstance
    have hh := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactCyclesIso_hom_iCycles S SheafForget.complexModuleForget) z
    change (K.iCycles (n + 1)) ((AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactCyclesIso S SheafForget.complexModuleForget).hom z) =
      (L.iCycles (n + 1)) z at hh
    rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk] at hh
    have hk := ConcreteCategory.congr_hom ((K.sc (n + 1)).moduleCatCyclesIso_inv_iCycles) c
    change (K.iCycles (n + 1)) ((K.sc (n + 1)).moduleCatCyclesIso.inv c) = c.val at hk
    exact hh.trans hk.symm
  have h := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.homologyπ_leftExactHomologyComparison S SheafForget.complexModuleForget) z
  rw [AlgebraicTopology.Cohomology.Singular.LeftExactHomologyIso.leftExactHomologyComparison_eq_mapHomologyIso',
    ShortComplex.mapHomologyIso'_eq_mapHomologyIso] at h
  change (ModuleGlobalSectionsForget.complexForgetHomologyIso K (n + 1)).hom (L.homologyπ (n + 1) z) =
    (K.homologyπ (n + 1)) ((AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactCyclesIso S SheafForget.complexModuleForget).hom z) at h
  rw [hz] at h
  exact h.trans (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_homologyπ K (n + 1) c).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.CochainForget
