import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CohomologyRing

/-! # Anticommutativity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.Anticommutativity.ModuleCup

noncomputable section

/-! Degree-one cup products anticommute already over the integral
coefficient ring. In particular their squares are killed by two before
any scalar extension. -/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleComplex OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CohomologyRing

universe u v

variable {R : Type u} [CommRing R] (A : CosimplicialObject (CommAlgCat.{v} R))

theorem cup_one_add_swap (x y : CohomologyRing.cohomology A 1) :
    ModuleCup.cohomologyCup A 1 1 x y + ModuleCup.cohomologyCup A 1 1 y x = 0 := by
  obtain ⟨cx, rfl⟩ := Module.CochainClasses.classMap_surjective (ModuleComplex.complex A) 1 x
  obtain ⟨cy, rfl⟩ := Module.CochainClasses.classMap_surjective (ModuleComplex.complex A) 1 y
  rw [ModuleCup.cup_class, ModuleCup.cup_class, ← map_add]
  apply (Module.CochainClasses.classMap_succ_eq_zero_iff (ModuleComplex.complex A) 1
    (ModuleCocycles.Cup.cycleCup A 1 1 cx cy + ModuleCocycles.Cup.cycleCup A 1 1 cy cx)).mpr
  obtain ⟨z, hz⟩ := OneCupBoundary.cup_sum_isBoundary (ModuleComplex.ringObject A)
    cx.1 cy.1 (ModuleComplex.cycle_differential A cx) (ModuleComplex.cycle_differential A cy)
  exact ⟨z, (ModuleComplex.complex_d_apply A 1 z).trans hz⟩

theorem two_smul_cup_self (x : CohomologyRing.cohomology A 1) :
    (2 : R) • ModuleCup.cohomologyCup A 1 1 x x = 0 := by
  rw [two_smul]
  exact cup_one_add_swap A x x

theorem inclusion_one_anticomm (x y : CohomologyRing.cohomology A 1) :
    CohomologyRing.inclusion A 1 x * CohomologyRing.inclusion A 1 y + CohomologyRing.inclusion A 1 y * CohomologyRing.inclusion A 1 x = 0 := by
  rw [← CohomologyRing.inclusion_cup, ← CohomologyRing.inclusion_cup, ← map_add, cup_one_add_swap, map_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.Anticommutativity.ModuleCup
