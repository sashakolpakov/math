import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Exact Injective -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactInjective.ExactInjectiveResolution

noncomputable section

/-! # Mapping injective resolutions through exact functors preserving injectives -/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] [F.PreservesInjectiveObjects]
  {Z : C} (I : InjectiveResolution Z)

def map : InjectiveResolution (F.obj Z) where
  cocomplex := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  injective n := by
    change Injective (F.obj (I.cocomplex.X n))
    infer_instance
  ι := ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).app Z).inv ≫
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactInjective.ExactInjectiveResolution
