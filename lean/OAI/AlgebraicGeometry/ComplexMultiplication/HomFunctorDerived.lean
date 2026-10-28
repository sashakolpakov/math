import OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Hom Functor Derived -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorDerived

noncomputable section

/-! # Original Hom-complex classes and actual derived functors

Actual additive exact functorial mapping agrees with the actual map on derived
morphisms, through the standard source and target comparison isomorphisms.
-/

open _root_.CategoryTheory Limits

universe v u₁ u₂

open _root_.CochainComplex.HomComplex

variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Abelian C]
  [Category.{v} D] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (A K : CochainComplex C ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Original Hom-complex classes map to the actual exact functor on derived morphisms. -/
theorem cohomologyClassToDerived_functorMap (n : ℤ) (z : CohomologyClass A K n) :
    HomPostcomp.cohomologyClassToDerived ((F.mapHomologicalComplex _).obj A)
        ((F.mapHomologicalComplex _).obj K) n (HomFunctorMap.HomComplex.functorMapClass F A K n z) =
      (ShiftedHom.mk₀ 0 rfl (F.mapDerivedCategoryFactors.inv.app A)).comp
        (((HomPostcomp.cohomologyClassToDerived A K n z).map F.mapDerivedCategory).comp
          (ShiftedHom.mk₀ 0 rfl (F.mapDerivedCategoryFactors.hom.app K))
            (zero_add n)) (add_zero n) := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [HomFunctorMap.HomComplex.functorMapClass_mk, HomPostcomp.cohomologyClassToDerived_mk,
    HomPostcomp.cohomologyClassToDerived_mk, HomFunctorShift.HomComplex.equivHomShift_symm_functorMapCocycle]
  let g : ShiftedHom A K n := Cocycle.equivHomShift.symm z
  change (g.map (F.mapHomologicalComplex (ComplexShape.up ℤ))).map DerivedCategory.Q =
    (ShiftedHom.mk₀ 0 rfl (F.mapDerivedCategoryFactors.inv.app A)).comp
      (((g.map DerivedCategory.Q).map F.mapDerivedCategory).comp
        (ShiftedHom.mk₀ 0 rfl (F.mapDerivedCategoryFactors.hom.app K))
          (zero_add n)) (add_zero n)
  rw [← ShiftedHom.comp_map, ← ShiftedHom.comp_map]
  exact (ShiftedHom.map_naturality_1 g F.mapDerivedCategoryFactors).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorDerived
