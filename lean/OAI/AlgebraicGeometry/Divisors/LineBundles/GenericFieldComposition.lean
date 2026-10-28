import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction

/-! # Generic Field Composition -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition.BundleCycles

noncomputable section

/-!
# LineBundleCycles: functoriality of actual generic-stalk maps

These identities follow from stalk specialization and actual germ maps.
They compare the geometric normalization maps with their local algebra.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

omit [IsIntegral Z] in
theorem genericFieldMap_congr {i j : X ⟶ Y} (hij : i = j)
    (hi : i (genericPoint X) = genericPoint Y) (hj : j (genericPoint X) = genericPoint Y) :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hi = Cycles.Functoriality.FunctionFields.Construction.genericFieldMap j hj := by
  subst j
  rfl

theorem genericFieldMap_comp (i : X ⟶ Y) (j : Y ⟶ Z)
    (hi : i (genericPoint X) = genericPoint Y) (hj : j (genericPoint Y) = genericPoint Z) :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (i ≫ j) ((congrArg j hi).trans hj) =
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap j hj ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hi := by
  simp only [Cycles.Functoriality.FunctionFields.Construction.genericFieldMap, TopCat.Presheaf.stalkCongr_hom,
    Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← j.stalkSpecializes_stalkMap_assoc (i (genericPoint X)) (genericPoint Y)
    (Inseparable.of_eq hi).specializes]
  have hc := Z.presheaf.stalkSpecializes_comp
    ((Inseparable.of_eq hi).specializes.map j.continuous) (Inseparable.of_eq hj).specializes
  exact congrArg (fun k : Z.presheaf.stalk (genericPoint Z) ⟶
    Z.presheaf.stalk (j (i (genericPoint X))) =>
      k ≫ j.stalkMap (i (genericPoint X)) ≫ i.stalkMap (genericPoint X)) hc.symm

omit [IsIntegral Z] in
theorem genericFieldMap_germ_appLE (i : X ⟶ Y)
    (hi : i (genericPoint X) = genericPoint Y)
    (U : Y.Opens) (V : X.Opens) [Nonempty U] [Nonempty V] (hV : V ≤ i ⁻¹ᵁ U) :
    Y.germToFunctionField U ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hi =
      i.appLE U V hV ≫ X.germToFunctionField V := by
  let : Nonempty (i ⁻¹ᵁ U) := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨⟨v.val, hV v.property⟩⟩
  rw [Deformation.FunctionField.BundleCycles.genericFieldMap_germOn, Scheme.Hom.appLE, Category.assoc]
  congr 1
  exact (X.presheaf.germ_res (homOfLE hV) (genericPoint X)
    (((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
      (by simpa using (show Nonempty V from inferInstance)))).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition.BundleCycles
