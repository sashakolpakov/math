import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjective

/-! # Yoneda Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Free.YonedaFunctor.FreeYonedaFunctor

noncomputable section

/-!
# Covariant free representable functors

Postcomposition of site arrows defines a covariant functor from site
objects to free representable presheaves, and then to their sheafifications.
These are the coefficient objects dual to native section evaluation.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v u' v'

variable (C : Type u) [Category.{v} C] (A : Type u') [Category.{v'} A]
  [HasCoproducts.{v} A] (M : A)

def presheaf : C ⥤ (Cᵒᵖ ⥤ A) :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (sigmaConst.obj M)

def presheafObjIso (P : C) : (presheaf C A M).obj P ≅ Presheaf.freeYoneda P M :=
  Iso.refl _

def sheaf (J : GrothendieckTopology C) [HasWeakSheafify J A] : C ⥤ Sheaf J A :=
  presheaf C A M ⋙ presheafToSheaf J A

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Free.YonedaFunctor.FreeYonedaFunctor
