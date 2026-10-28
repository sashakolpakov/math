import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CycleCoordinates

/-! # Hom Complex Cycle Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HomComplexCycleCoordinates

noncomputable section

/-! The quotient of Hom-complex cocycles agrees with their actual homology representatives. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CochainComplex _root_.CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  (A K : CochainComplex C ℤ) (n : ℤ) (z : Cocycle A K n)

theorem homComplexCocycle_closed : (A.HomComplex K).d n (n + 1) z.val = 0 :=
  Cocycle.δ_eq_zero z (n + 1)

theorem homComplexCycles_coordinates :
    (leftHomologyData A K n).cyclesIso.hom
      (Abelian.CycleCoordinates.abelianIntegerCycles (A.HomComplex K) n z.val (homComplexCocycle_closed A K n z)) = z := by
  apply Cocycle.ext
  have h := ConcreteCategory.congr_hom (leftHomologyData A K n).cyclesIso_hom_comp_i
    (Abelian.CycleCoordinates.abelianIntegerCycles (A.HomComplex K) n z.val (homComplexCocycle_closed A K n z))
  change _ = (A.HomComplex K).iCycles n
    (Abelian.CycleCoordinates.abelianIntegerCycles (A.HomComplex K) n z.val (homComplexCocycle_closed A K n z)) at h
  exact h.trans (Abelian.CycleCoordinates.abelianIntegerCycles_i (A.HomComplex K) n z.val (homComplexCocycle_closed A K n z))

theorem homComplexCycleClass_coordinates :
    homologyAddEquiv A K n
      (Abelian.CycleCoordinates.abelianIntegerCycleClass (A.HomComplex K) n z.val (homComplexCocycle_closed A K n z)) =
        CohomologyClass.mk z := by
  have h := ConcreteCategory.congr_hom
    (leftHomologyData A K n).homologyπ_comp_homologyIso_hom
      (Abelian.CycleCoordinates.abelianIntegerCycles (A.HomComplex K) n z.val (homComplexCocycle_closed A K n z))
  change homologyAddEquiv A K n
      (Abelian.CycleCoordinates.abelianIntegerCycleClass (A.HomComplex K) n z.val (homComplexCocycle_closed A K n z)) =
    CohomologyClass.mk ((leftHomologyData A K n).cyclesIso.hom
      (Abelian.CycleCoordinates.abelianIntegerCycles (A.HomComplex K) n z.val (homComplexCocycle_closed A K n z))) at h
  rw [homComplexCycles_coordinates] at h
  exact h

theorem homComplexCohomologyClass_coordinates :
    (homologyAddEquiv A K n).symm (CohomologyClass.mk z) =
      Abelian.CycleCoordinates.abelianIntegerCycleClass (A.HomComplex K) n z.val (homComplexCocycle_closed A K n z) :=
  (homologyAddEquiv A K n).symm_apply_eq.mpr (homComplexCycleClass_coordinates A K n z).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HomComplexCycleCoordinates
