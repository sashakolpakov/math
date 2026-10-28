import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.IntrinsicOperators
import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechClasses

/-! # Sheaf Boundaries -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.SheafBoundaries

noncomputable section

/-! An actual Cech coboundary has zero native and sheaf cohomology class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

theorem abelianCechNativeClass_eq_zero_of_boundary
    (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (k : Abelian.CechCoordinates.AbelianCechCochain F U (n + 1)) (hk : Abelian.CechCoordinates.abelianCechDelta F U (n + 1) k = 0)
    (b : Abelian.CechCoordinates.AbelianCechCochain F U n) (hb : Abelian.CechCoordinates.abelianCechDelta F U n b = k) :
    Abelian.CechClasses.abelianCechNativeClass U F n k hk = 0 := by
  let L := (CategoryTheory.cechComplexFunctor U).obj F
  let x := (Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)).symm k
  have hx := Abelian.CechClasses.abelianCechNative_closed U F (n + 1) k hk
  have hz : L.d (n + 1) (n + 2) 0 = 0 := map_zero _
  have he := SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyπ_cyclesMk_eq_of_sub_eq_boundary n L x 0 hx hz
    ((Abelian.CechCoordinates.abelianCechCoordinates F U n).symm b) (by
      rw [sub_zero, IntrinsicOperators.abelianCechCoordinates_symm_d, hb])
  have hc : SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n L 0 hz = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (L.iCycles (n + 1))).mp inferInstance
    rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, map_zero]
  change L.homologyπ (n + 1) (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n L x hx) = 0
  rw [he, hc, map_zero]

theorem abelianCechSheafClass_eq_zero_of_boundary
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (hU : ⨆ i, U i = ⊤) (n : ℕ)
    (k : Abelian.CechCoordinates.AbelianCechCochain F.obj U (n + 1)) (hk : Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) k = 0)
    (b : Abelian.CechCoordinates.AbelianCechCochain F.obj U n) (hb : Abelian.CechCoordinates.abelianCechDelta F.obj U n b = k) :
    Abelian.CechClasses.abelianCechSheafClass U F hU n k hk = 0 := by
  unfold Abelian.CechClasses.abelianCechSheafClass
  rw [abelianCechNativeClass_eq_zero_of_boundary U F.obj n k hk b hb, map_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.SheafBoundaries
