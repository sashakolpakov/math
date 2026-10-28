import Mathlib

/-! # Derived Equivalence Is -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedEquivalenceIs.DerivedEquivalence

noncomputable section

/-! An additive equivalence induces an equivalence of the actual derived categories. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (e : C ≌ D) [e.functor.Additive]

theorem induced_isEquivalence : e.functor.mapDerivedCategory.IsEquivalence := by
  let Φ := e.functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  let Ψ := e.inverse.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  let ec := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let : Φ.IsLocalizedEquivalence :=
    Φ.isLocalizedEquivalence_of_unit_of_unit Ψ ec.unitIso.hom ec.counitIso.inv
      (fun K => by
        change QuasiIso ((ec.unitIso.app K).hom)
        infer_instance)
      (fun K => by
        change QuasiIso ((ec.counitIso.app K).inv)
        infer_instance)
  change (Φ.localizedFunctor DerivedCategory.Q DerivedCategory.Q).IsEquivalence
  infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedEquivalenceIs.DerivedEquivalence
