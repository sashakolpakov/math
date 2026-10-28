import OAI.AlgebraicGeometry.Comparison.Betti.Derived.Cocycle

/-! # Hom Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HomFunctor.Ext

noncomputable section

/-! The comparison on Hom complexes is induced by the actual exact functor and coefficient morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u u' v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] {A : C} {A' : D}
  (a : A' ⟶ F.obj A) {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}
  (β : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)

def integerHomFunctorComparison : IntegerAcyclicHomComplex.Ext.integerHomComplex A K ⟶ IntegerAcyclicHomComplex.Ext.integerHomComplex A' L where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z => a ≫ F.map z ≫ β.f n
      map_zero' := by
        change a ≫ F.map (0 : A ⟶ K.X n) ≫ β.f n = 0
        erw [Functor.map_zero, zero_comp, comp_zero]
      map_add' := by
        intro z z'
        change A ⟶ K.X n at z z'
        erw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
        rfl }
  comm' n m _ := by
    ext z
    change A ⟶ K.X n at z
    change (a ≫ F.map z ≫ β.f n) ≫ L.d n m = a ≫ F.map (z ≫ K.d n m) ≫ β.f m
    erw [Category.assoc, Category.assoc, β.comm]
    erw [F.map_comp]
    exact congrArg (a ≫ ·) (Category.assoc _ _ _).symm

theorem integerHomFunctorComparison_f (n : ℤ) (z : A ⟶ K.X n) :
    (integerHomFunctorComparison F a β).f n z = a ≫ F.map z ≫ β.f n := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.HomFunctor.Ext
