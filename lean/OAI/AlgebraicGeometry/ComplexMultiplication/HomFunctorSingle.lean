import OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorMap
import OAI.Algebra.Homology.HomComplexSingle

/-! # Hom Functor Single -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorSingle.HomComplex

noncomputable section

/-! # Actual functorial transport of single-source cochains -/

open _root_.CategoryTheory Limits _root_.CochainComplex.HomComplex

universe v u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Abelian C]
  [Category.{v} D] [Abelian D] (F : C ⥤ D) [F.Additive]
  (A : C) (K : CochainComplex C ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual single-source transport maps each original cochain by the original functor. -/
theorem fromSingleEquiv_functorMap_precomp {A' : D} (c : A' ⟶ F.obj A)
    (n : ℤ) (z : Cochain ((CochainComplex.singleFunctor C 0).obj A) K n) :
    Cochain.fromSingleEquiv (zero_add n)
        ((Cochain.ofHom ((CochainComplex.singleFunctor D 0).map c ≫
          (F.mapCochainComplexSingleFunctor 0).inv.app A)).comp (z.map F) (zero_add n)) =
      c ≫ F.map (Cochain.fromSingleEquiv (zero_add n) z) := by
  simp [Cochain.fromSingleEquiv, Cochain.ofHom, Cochain.map,
    Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self, Category.assoc]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorSingle.HomComplex
