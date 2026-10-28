import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechLowDegreeRestrictions

/-! # Cech Low Degree Differentials -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechLowDegreeDifferentials

noncomputable section

/-! The first two Cech differentials in ordinary section coordinates. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechTupleCoordinates

private theorem alternating_two {A : Type*} [AddCommGroup A] (v : Fin 2 → A) :
    (∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) • v k) = v 0 - v 1 := by
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_zsmul,
    Fin.val_one, pow_one, neg_one_zsmul, sub_eq_add_neg]

private theorem alternating_three {A : Type*} [AddCommGroup A] (v : Fin 3 → A) :
    (∑ k : Fin 3, (-1 : ℤ) ^ (k : ℕ) • v k) = v 0 - v 1 + v 2 := by
  simp only [Fin.sum_univ_three, Fin.val_zero, pow_zero, one_zsmul,
    Fin.val_one, pow_one, neg_one_zsmul, Fin.val_two, neg_one_sq, sub_eq_add_neg]

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} (U : ι → X.Opens)

theorem differential_zero (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 0) (i j : ι) :
    CechTuplePi.Construction.CechTupleCoordinates.one π M U ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d 0 1 z) i j =
      M.presheaf.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (CechTuplePi.Construction.CechTupleCoordinates.zero π M U z j) -
        M.presheaf.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (CechTuplePi.Construction.CechTupleCoordinates.zero π M U z i) := by
  rw [CechLowDegreeRestrictions.Construction.CechTupleCoordinates.one_eq_restricted, CechDifferentialValues.Construction.CechTupleCoordinates.restricted_differential, alternating_two]
  congr 1
  · exact (CechDifferentialValues.Construction.CechTupleCoordinates.restricted_index π M U 0 z _ _ (CechLowDegreeRestrictions.Construction.CechTupleCoordinates.pair_delete_zero i j) _ _ _).trans
      (CechLowDegreeRestrictions.Construction.CechTupleCoordinates.restricted_zero π M U z j (U i ⊓ U j) inf_le_right)
  · exact (CechDifferentialValues.Construction.CechTupleCoordinates.restricted_index π M U 0 z _ _ (CechLowDegreeRestrictions.Construction.CechTupleCoordinates.pair_delete_one i j) _ _ _).trans
      (CechLowDegreeRestrictions.Construction.CechTupleCoordinates.restricted_zero π M U z i (U i ⊓ U j) inf_le_left)

theorem differential_one (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 1) (i j k : ι) :
    CechTuplePi.Construction.CechTupleCoordinates.two π M U ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d 1 2 z) i j k =
      M.presheaf.map (homOfLE (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j from inf_le_left)).op
        (CechTuplePi.Construction.CechTupleCoordinates.one π M U z i j) +
      M.presheaf.map (homOfLE (show (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k from
        le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op (CechTuplePi.Construction.CechTupleCoordinates.one π M U z j k) -
      M.presheaf.map (homOfLE (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (CechTuplePi.Construction.CechTupleCoordinates.one π M U z i k) := by
  rw [CechLowDegreeRestrictions.Construction.CechTupleCoordinates.two_eq_restricted, CechDifferentialValues.Construction.CechTupleCoordinates.restricted_differential, alternating_three]
  have h0 := (CechDifferentialValues.Construction.CechTupleCoordinates.restricted_index π M U 1 z _ _ (CechLowDegreeRestrictions.Construction.CechTupleCoordinates.triple_delete_zero i j k) _
    ((CechTuplePi.Construction.CechTupleCoordinates.intersection_two U (i, j, k)).ge.trans (leOfHom (CechDifferentialValues.Construction.CechTupleCoordinates.face U 1 ![i, j, k] 0))) _).trans
    (CechLowDegreeRestrictions.Construction.CechTupleCoordinates.restricted_one π M U z j k ((U i ⊓ U j) ⊓ U k)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
  have h1 := (CechDifferentialValues.Construction.CechTupleCoordinates.restricted_index π M U 1 z _ _ (CechLowDegreeRestrictions.Construction.CechTupleCoordinates.triple_delete_one i j k) _
    ((CechTuplePi.Construction.CechTupleCoordinates.intersection_two U (i, j, k)).ge.trans (leOfHom (CechDifferentialValues.Construction.CechTupleCoordinates.face U 1 ![i, j, k] 1))) _).trans
    (CechLowDegreeRestrictions.Construction.CechTupleCoordinates.restricted_one π M U z i k ((U i ⊓ U j) ⊓ U k)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
  have h2 := (CechDifferentialValues.Construction.CechTupleCoordinates.restricted_index π M U 1 z _ _ (CechLowDegreeRestrictions.Construction.CechTupleCoordinates.triple_delete_two i j k) _
    ((CechTuplePi.Construction.CechTupleCoordinates.intersection_two U (i, j, k)).ge.trans (leOfHom (CechDifferentialValues.Construction.CechTupleCoordinates.face U 1 ![i, j, k] 2))) _).trans
    (CechLowDegreeRestrictions.Construction.CechTupleCoordinates.restricted_one π M U z i j ((U i ⊓ U j) ⊓ U k) inf_le_left)
  rw [h0, h1, h2]
  abel

end Construction.CechTupleCoordinates

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechLowDegreeDifferentials
