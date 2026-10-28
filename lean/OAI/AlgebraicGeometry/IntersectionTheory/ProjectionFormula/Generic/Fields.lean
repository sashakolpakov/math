import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.DivisorRestriction

/-! # Fields -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Fields

noncomputable section

/-! Functoriality of the actual generic-stalk maps, used to compare the
global and local normalization field identifications. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

omit [IsIntegral Z] in
theorem genericFieldMap_congr {i j : X ⟶ Y} (hij : i = j)
    (hi : i (genericPoint X) = genericPoint Y)
    (hj : j (genericPoint X) = genericPoint Y) :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hi = Cycles.Functoriality.FunctionFields.Construction.genericFieldMap j hj := by
  subst j
  rfl

theorem genericFieldMap_comp (i : X ⟶ Y) (j : Y ⟶ Z)
    (hi : i (genericPoint X) = genericPoint Y)
    (hj : j (genericPoint Y) = genericPoint Z) :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (i ≫ j) ((congrArg j hi).trans hj) =
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap j hj ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hi := by
  simp only [Cycles.Functoriality.FunctionFields.Construction.genericFieldMap, TopCat.Presheaf.stalkCongr_hom,
    Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← j.stalkSpecializes_stalkMap_assoc (i (genericPoint X)) (genericPoint Y)
    (Inseparable.of_eq hi).specializes]
  simp only [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

omit [IsIntegral Z] in
theorem genericFieldMap_germ_open (i : X ⟶ Y)
    (hi : i (genericPoint X) = genericPoint Y)
    (U : Y.Opens) [Nonempty U] [Nonempty (i ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hi =
      i.app U ≫ X.germToFunctionField (i ⁻¹ᵁ U) := by
  simp only [Cycles.Functoriality.FunctionFields.Construction.genericFieldMap, TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact i.germ_stalkMap U (genericPoint X)
    (((genericPoint_spec X).mem_open_set_iff (i ⁻¹ᵁ U).isOpen).mpr
      (by simpa using (show Nonempty (i ⁻¹ᵁ U) from inferInstance)))

omit [IsIntegral Z] in
theorem genericFieldMap_germ_appLE (i : X ⟶ Y)
    (hi : i (genericPoint X) = genericPoint Y)
    (U : Y.Opens) (V : X.Opens) [Nonempty U] [Nonempty V] (hV : V ≤ i ⁻¹ᵁ U) :
    Y.germToFunctionField U ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hi =
      i.appLE U V hV ≫ X.germToFunctionField V := by
  let : Nonempty (i ⁻¹ᵁ U) := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨⟨v.val, hV v.property⟩⟩
  rw [genericFieldMap_germ_open, Scheme.Hom.appLE, Category.assoc]
  congr 1
  exact (X.presheaf.germ_res (homOfLE hV) (genericPoint X)
    (((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
      (by simpa using (show Nonempty V from inferInstance)))).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Fields
