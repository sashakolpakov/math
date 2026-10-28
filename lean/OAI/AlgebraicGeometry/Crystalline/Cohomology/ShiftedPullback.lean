import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.Algebra.Group.Int.Defs

/-! # Shifted Pullback -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPullback.ShiftedPullbackFactor

noncomputable section

/-! # A factorization identity for functors that commute with shifts -/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
  {D : Type w} [Category.{z} D] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ]
  {A M M' : C} {N N' : D} (iM : M' ⟶ M) (iN : N' ⟶ N)
  (p : F.obj M ⟶ N) (p' : F.obj M' ⟶ N')
  (hp : p' ≫ iN = F.map iM ≫ p) (n : ℤ) (a : A ⟶ M'⟦n⟧)

include hp in
theorem factor :
    F.map (a ≫ (shiftFunctor C n).map iM) ≫ (F.commShiftIso n).hom.app M ≫ (shiftFunctor D n).map p =
      (F.map a ≫ (F.commShiftIso n).hom.app M' ≫ (shiftFunctor D n).map p') ≫ (shiftFunctor D n).map iN := by
  rw [F.map_comp]
  simp only [Category.assoc]
  have hn : F.map ((shiftFunctor C n).map iM) ≫ (F.commShiftIso n).hom.app M =
      (F.commShiftIso n).hom.app M' ≫ (shiftFunctor D n).map (F.map iM) :=
    (F.commShiftIso n).hom.naturality iM
  have hna := congrArg (fun z => z ≫ (shiftFunctor D n).map p) hn
  simp only [Category.assoc] at hna
  rw [hna]
  rw [← Functor.map_comp, ← hp, Functor.map_comp]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPullback.ShiftedPullbackFactor
