import OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport

/-! # Generic Field Composition -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.GenericFieldComposition.Constructions

noncomputable section

/-!
# ThomClass: functoriality of actual generic-stalk maps

These identities follow from stalk specialization and actual germ maps.
They compare the geometric normalization maps with their local algebra.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions

universe u
variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

omit [IsIntegral Z] in
theorem genericFieldMap_congr {i j : X ⟶ Y} (hij : i = j)
    (hi : i (genericPoint X) = genericPoint Y) (hj : j (genericPoint X) = genericPoint Y) :
    RationalOrderTransport.Constructions.genericFieldMap i hi = RationalOrderTransport.Constructions.genericFieldMap j hj := by
  subst j
  rfl

theorem genericFieldMap_comp (i : X ⟶ Y) (j : Y ⟶ Z)
    (hi : i (genericPoint X) = genericPoint Y) (hj : j (genericPoint Y) = genericPoint Z) :
    RationalOrderTransport.Constructions.genericFieldMap (i ≫ j) ((congrArg j hi).trans hj) =
      RationalOrderTransport.Constructions.genericFieldMap j hj ≫ RationalOrderTransport.Constructions.genericFieldMap i hi := by
  simp only [RationalOrderTransport.Constructions.genericFieldMap, TopCat.Presheaf.stalkCongr_hom,
    Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← j.stalkSpecializes_stalkMap_assoc (i (genericPoint X)) (genericPoint Y)
    (Inseparable.of_eq hi).specializes]
  have hc := Z.presheaf.stalkSpecializes_comp
    ((Inseparable.of_eq hi).specializes.map j.continuous) (Inseparable.of_eq hj).specializes
  exact congrArg (fun k : Z.presheaf.stalk (genericPoint Z) ⟶
    Z.presheaf.stalk (j (i (genericPoint X))) =>
      k ≫ j.stalkMap (i (genericPoint X)) ≫ i.stalkMap (genericPoint X)) hc.symm

omit [IsIntegral X] [IsIntegral Y] [IsIntegral Z] in
/-- Generic-stalk pullback agrees with pullback on every nonempty open. -/
theorem genericFieldMap_germOn {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) (hη : i (genericPoint A) = genericPoint B)
    (U : B.Opens) [Nonempty U] [Nonempty (i ⁻¹ᵁ U)] :
    B.germToFunctionField U ≫ RationalOrderTransport.Constructions.genericFieldMap i hη =
      i.app U ≫ A.germToFunctionField (i ⁻¹ᵁ U) := by
  simp only [RationalOrderTransport.Constructions.genericFieldMap, TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
  have hx : genericPoint A ∈ i ⁻¹ᵁ U :=
    (genericPoint_spec A).mem_open_set_iff (i ⁻¹ᵁ U).isOpen |>.mpr
      (by simpa using (show Nonempty (i ⁻¹ᵁ U) from inferInstance))
  have h := B.presheaf.germ_stalkSpecializes
    (show genericPoint B ∈ U from hη ▸ hx) (Inseparable.of_eq hη).specializes
  exact (congrArg
    (fun k : Γ(B, U) ⟶ B.presheaf.stalk (i (genericPoint A)) => k ≫ i.stalkMap (genericPoint A)) h).trans
    (i.germ_stalkMap U (genericPoint A) hx)

omit [IsIntegral Z] in
theorem genericFieldMap_germ_appLE (i : X ⟶ Y)
    (hi : i (genericPoint X) = genericPoint Y)
    (U : Y.Opens) (V : X.Opens) [Nonempty U] [Nonempty V] (hV : V ≤ i ⁻¹ᵁ U) :
    Y.germToFunctionField U ≫ RationalOrderTransport.Constructions.genericFieldMap i hi =
      i.appLE U V hV ≫ X.germToFunctionField V := by
  let : Nonempty (i ⁻¹ᵁ U) := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨⟨v.val, hV v.property⟩⟩
  rw [genericFieldMap_germOn, Scheme.Hom.appLE, Category.assoc]
  congr 1
  exact (X.presheaf.germ_res (homOfLE hV) (genericPoint X)
    (((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
      (by simpa using (show Nonempty V from inferInstance)))).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.GenericFieldComposition.Constructions
