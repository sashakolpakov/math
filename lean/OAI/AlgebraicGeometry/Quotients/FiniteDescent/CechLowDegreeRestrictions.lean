import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechDifferentialValues

/-! # Cech Low Degree Restrictions -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechLowDegreeRestrictions

noncomputable section

/-! Low-degree tuple coordinates and restrictions to smaller opens. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechTupleCoordinates

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} (U : ι → X.Opens)

theorem restricted_zero (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 0)
    (i : ι) (W : X.Opens) (hW : W ≤ U i) :
    CechDifferentialValues.Construction.CechTupleCoordinates.restrictedValue π M U 0 z (fun _ => i) W (hW.trans (CechTuplePi.Construction.CechTupleCoordinates.intersection_zero U i).ge) =
      M.presheaf.map (homOfLE hW).op (CechTuplePi.Construction.CechTupleCoordinates.zero π M U z i) := by
  rw [CechTupleValues.Construction.CechTupleCoordinates.zero_apply, ← M.presheaf.map_comp_apply]
  rfl

theorem restricted_one (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 1)
    (i j : ι) (W : X.Opens) (hW : W ≤ U i ⊓ U j) :
    CechDifferentialValues.Construction.CechTupleCoordinates.restrictedValue π M U 1 z ![i, j] W (hW.trans (CechTuplePi.Construction.CechTupleCoordinates.intersection_one U (i, j)).ge) =
      M.presheaf.map (homOfLE hW).op (CechTuplePi.Construction.CechTupleCoordinates.one π M U z i j) := by
  rw [CechTupleValues.Construction.CechTupleCoordinates.one_apply, ← M.presheaf.map_comp_apply]
  rfl

theorem one_eq_restricted (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 1) (i j : ι) :
    CechTuplePi.Construction.CechTupleCoordinates.one π M U z i j = CechDifferentialValues.Construction.CechTupleCoordinates.restrictedValue π M U 1 z ![i, j] (U i ⊓ U j)
      (CechTuplePi.Construction.CechTupleCoordinates.intersection_one U (i, j)).ge :=
  CechTupleValues.Construction.CechTupleCoordinates.one_apply π M U z i j

theorem two_eq_restricted (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 2) (i j k : ι) :
    CechTuplePi.Construction.CechTupleCoordinates.two π M U z i j k = CechDifferentialValues.Construction.CechTupleCoordinates.restrictedValue π M U 2 z ![i, j, k] ((U i ⊓ U j) ⊓ U k)
      (CechTuplePi.Construction.CechTupleCoordinates.intersection_two U (i, j, k)).ge :=
  CechTupleValues.Construction.CechTupleCoordinates.two_apply π M U z i j k

theorem pair_delete_zero (i j : ι) : CechDifferentialValues.Construction.CechTupleCoordinates.delete 0 ![i, j] 0 = fun _ => j := by
  funext k
  fin_cases k
  rfl

theorem pair_delete_one (i j : ι) : CechDifferentialValues.Construction.CechTupleCoordinates.delete 0 ![i, j] 1 = fun _ => i := by
  funext k
  fin_cases k
  rfl

theorem triple_delete_zero (i j k : ι) : CechDifferentialValues.Construction.CechTupleCoordinates.delete 1 ![i, j, k] 0 = ![j, k] := by
  funext a
  fin_cases a <;> rfl

theorem triple_delete_one (i j k : ι) : CechDifferentialValues.Construction.CechTupleCoordinates.delete 1 ![i, j, k] 1 = ![i, k] := by
  funext a
  fin_cases a <;> rfl

theorem triple_delete_two (i j k : ι) : CechDifferentialValues.Construction.CechTupleCoordinates.delete 1 ![i, j, k] 2 = ![i, j] := by
  funext a
  fin_cases a <;> rfl

end Construction.CechTupleCoordinates

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechLowDegreeRestrictions
