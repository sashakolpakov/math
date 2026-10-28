import OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorMap
import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Hom Functor Shift -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorShift.HomComplex

noncomputable section

/-! # Genuine Hom-complex functorial mapping and shifts

The actual componentwise cocycle map gives the expected morphism into the
shifted complex, with the standard shift comparison for an additive functor.
-/

open _root_.CategoryTheory Limits

universe v u₁ u₂

open _root_.CochainComplex.HomComplex

variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Abelian C]
  [Category.{v} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] (A K : CochainComplex C ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual functorial cocycle map respects the original morphism-to-shift interpretation. -/
theorem equivHomShift_symm_functorMapCocycle (n : ℤ) (z : Cocycle A K n) :
    Cocycle.equivHomShift.symm (HomFunctorMap.HomComplex.functorMapCocycle F A K n z) =
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Cocycle.equivHomShift.symm z) ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app K := by
  ext i
  simp only [HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f,
    Cocycle.rightShift_coe, Cochain.rightShift, HomFunctorMap.HomComplex.functorMapCocycle,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorShift.HomComplex
