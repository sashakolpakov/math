import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.Functor

/-! # Coefficient Derived Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CoefficientDerivedNaturality.Ext

noncomputable section

/-! The normalized derived coefficient map commutes with actual comparison squares of complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u u' v w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {K K' : CochainComplex C ℤ} {L L' : CochainComplex D ℤ}
  (β : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
  (β' : (F.mapHomologicalComplex (.up ℤ)).obj K' ⟶ L')
  (e : K ⟶ K') (d : L ⟶ L')
  (h : (F.mapHomologicalComplex (.up ℤ)).map e ≫ β' = β ≫ d)

include h in
theorem coefficientDerivedMap_factor_square :
    F.mapDerivedCategory.map (DerivedCategory.Q.map e) ≫
        (F.mapDerivedCategoryFactors.hom.app K' ≫ DerivedCategory.Q.map β') =
      (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map β) ≫ DerivedCategory.Q.map d := by
  have hn := F.mapDerivedCategoryFactors.hom.naturality e
  change F.mapDerivedCategory.map (DerivedCategory.Q.map e) ≫ F.mapDerivedCategoryFactors.hom.app K' =
    F.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map e) at hn
  calc
    _ = (F.mapDerivedCategory.map (DerivedCategory.Q.map e) ≫ F.mapDerivedCategoryFactors.hom.app K') ≫
        DerivedCategory.Q.map β' := (Category.assoc _ _ _).symm
    _ = (F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map e)) ≫
          DerivedCategory.Q.map β' := congrArg (· ≫ DerivedCategory.Q.map β') hn
    _ = F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map e ≫ β') :=
      (Category.assoc _ _ _).trans
        (congrArg (F.mapDerivedCategoryFactors.hom.app K ≫ ·)
          (DerivedCategory.Q.map_comp ((F.mapHomologicalComplex (.up ℤ)).map e) β').symm)
    _ = F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map (β ≫ d) :=
      congrArg (fun a => F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map a) h
    _ = _ := (congrArg (F.mapDerivedCategoryFactors.hom.app K ≫ ·)
      (DerivedCategory.Q.map_comp β d)).trans (Category.assoc _ _ _).symm

theorem derivedShiftedHom_map_postcomp {A : DerivedCategory C} {n : ℤ}
    (x : A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :
    ShiftedHom.map (x ≫ (DerivedCategory.Q.map e)⟦n⟧') F.mapDerivedCategory =
      ShiftedHom.map x F.mapDerivedCategory ≫
        (F.mapDerivedCategory.map (DerivedCategory.Q.map e))⟦n⟧' := by
  have h := ShiftedHom.map_comp x (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Q.map e))
    (zero_add n) F.mapDerivedCategory
  simpa only [ShiftedHom.comp_mk₀, ShiftedHom.map_mk₀] using h

include h in
theorem coefficientDerivedMap_naturality (A : C) (A' : D) (a : A' ⟶ F.obj A) (n : ℤ)
    (x : (DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :
    Acyclic.Functor.Ext.coefficientDerivedMap F A A' a K' L' β' n (x ≫ (DerivedCategory.Q.map e)⟦n⟧') =
      Acyclic.Functor.Ext.coefficientDerivedMap F A A' a K L β n x ≫ (DerivedCategory.Q.map d)⟦n⟧' := by
  unfold Acyclic.Functor.Ext.coefficientDerivedMap
  rw [derivedShiftedHom_map_postcomp F e]
  have hs := congrArg (fun t => t⟦n⟧') (coefficientDerivedMap_factor_square F β β' e d h)
  let S := shiftFunctor (DerivedCategory D) n
  have hs' := (S.map_comp (F.mapDerivedCategory.map (DerivedCategory.Q.map e))
    (F.mapDerivedCategoryFactors.hom.app K' ≫ DerivedCategory.Q.map β')).symm.trans
      (hs.trans (S.map_comp (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map β)
        (DerivedCategory.Q.map d)))
  simp only [Category.assoc]
  exact congrArg (fun t => (DerivedCategory.singleFunctor D 0).map a ≫
    (F.mapDerivedCategorySingleFunctor 0).inv.app A ≫ ShiftedHom.map x F.mapDerivedCategory ≫ t) hs'

end

end OAI.AlgebraicGeometry.Comparison.Betti.CoefficientDerivedNaturality.Ext
