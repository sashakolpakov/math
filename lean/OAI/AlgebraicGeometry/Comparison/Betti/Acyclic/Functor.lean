import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.FunctorNaturality

/-! # Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.Functor.Ext

noncomputable section

/-! A quasi-isomorphism of the actual Hom comparison makes the normalized derived coefficient map bijective. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe u u' v w w' e e'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (A : C) (A' : D) (a : A' ⟶ F.obj A)
  (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
  (β : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) (n : ℤ)

def coefficientDerivedMap
    (x : (DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :
    (DerivedCategory.singleFunctor D 0).obj A' ⟶ (DerivedCategory.Q.obj L)⟦n⟧ :=
  (DerivedCategory.singleFunctor D 0).map a ≫
    (F.mapDerivedCategorySingleFunctor 0).inv.app A ≫
      ShiftedHom.map x F.mapDerivedCategory ≫
        (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map β)⟦n⟧'

variable [EnoughInjectives C] [HasExt.{e} C] [EnoughInjectives D] [HasExt.{e'} D]
  (b c : ℤ) [K.IsStrictlyGE b] [L.IsStrictlyGE c]

include b c in
theorem coefficientDerivedMap_bijective_of_acyclic
    (hK : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext A' (L.X p) (q + 1)))
    (hβ : QuasiIso (HomFunctor.Ext.integerHomFunctorComparison F a β)) :
    Function.Bijective (coefficientDerivedMap F A A' a K L β n) := by
  let s := HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A K b hK n
  let t := HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A' L c hL n
  let p := HomologicalComplex.homologyMap (HomFunctor.Ext.integerHomFunctorComparison F a β) n
  have hp : IsIso p := (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance
  have hb : Function.Bijective p := ConcreteCategory.bijective_of_isIso p
  have hEq : coefficientDerivedMap F A A' a K L β n = t ∘ p ∘ s.symm := by
    funext x
    have h := FunctorNaturality.Ext.acyclicHomCohomologyDerivedEquiv_functor F A A' a K L b c hK hL β n (s.symm x)
    change t (p (s.symm x)) = coefficientDerivedMap F A A' a K L β n (s (s.symm x)) at h
    rw [s.apply_symm_apply] at h
    exact h.symm
  rw [hEq]
  exact t.bijective.comp (hb.comp s.symm.bijective)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.Functor.Ext
