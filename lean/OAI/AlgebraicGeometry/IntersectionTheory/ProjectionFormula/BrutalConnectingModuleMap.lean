import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalConnectingMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SingleShiftCoordinates

/-! # Brutal Connecting Module Map -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalConnectingModuleMap

noncomputable section

/-! After shifting the target column, its connecting map is exactly the
single-complex map induced by the original module differential. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CochainComplex _root_.CochainComplex.HomComplex

variable (R : Type) [CommRing R] (A : CochainComplex (ModuleCat.{0} R) ℤ) (p : ℤ)

theorem eq_module_map :
    Cocycle.homOf ((BrutalConnectingMap.columnConnecting R A p).rightShift 1 0 (zero_add 1)) ≫
      (((CochainComplex.singleFunctors (ModuleCat.{0} R)).shiftIso 1 (-((p + 1) + 1)) (-(p + 1))
        (by omega)).hom.app (A.X (-(p + 1)))) =
    (CochainComplex.singleFunctor (ModuleCat.{0} R) (-((p + 1) + 1))).map
      (A.d (-((p + 1) + 1)) (-(p + 1))) := by
  let z : Cocycle
      ((HomologicalComplex.single (ModuleCat.{0} R) (.up ℤ) (-((p + 1) + 1))).obj (A.X (-((p + 1) + 1))))
      ((HomologicalComplex.single (ModuleCat.{0} R) (.up ℤ) (-(p + 1))).obj (A.X (-(p + 1)))) 1 :=
    BrutalConnectingMap.columnConnecting R A p
  change Cocycle.homOf (z.rightShift 1 0 (zero_add 1)) ≫ _ =
    (HomologicalComplex.single (ModuleCat.{0} R) (.up ℤ) (-((p + 1) + 1))).map _
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, Cocycle.homOf_f, Cocycle.rightShift_coe,
    Cochain.rightShift_v _ 1 0 (zero_add 1) (-((p + 1) + 1)) (-((p + 1) + 1))
      (add_zero _) (-(p + 1)) (by omega), HomologicalComplex.single_map_f_self]
  rw [← cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) (-((p + 1) + 1)) (A.X (-(p + 1)))).hom,
    ← cancel_epi (HomologicalComplex.singleObjXSelf (.up ℤ) (-((p + 1) + 1)) (A.X (-((p + 1) + 1)))).inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    _ = (HomologicalComplex.singleObjXSelf (.up ℤ) (-((p + 1) + 1)) (A.X (-((p + 1) + 1)))).inv ≫
        z.1.v (-((p + 1) + 1)) (-(p + 1)) (by omega) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) (-(p + 1)) (A.X (-(p + 1)))).hom := by
      congr 1
      congr 1
      exact SingleShiftCoordinates.shiftIso_term R (A.X (-(p + 1))) 1
        (-((p + 1) + 1)) (-(p + 1)) (by omega)
    _ = _ := BrutalConnectingMap.columnConnecting_value R A p

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalConnectingModuleMap
