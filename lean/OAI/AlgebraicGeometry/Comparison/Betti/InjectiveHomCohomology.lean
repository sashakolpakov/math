import OAI.AlgebraicGeometry.Comparison.Betti.HomComplexSingleIso
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Linear.Basic

/-! # Injective Hom Cohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomCohomology.Ext

noncomputable section

/-! Ordinary Hom cohomology computes derived morphisms into an actual K-injective complex. -/

open _root_.CategoryTheory _root_.CochainComplex _root_.CochainComplex.HomComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (A : C) (K : CochainComplex C ℤ) [K.IsKInjective] (n : ℤ)

def kInjectiveCohomologyClassDerivedEquiv :
    CohomologyClass ((CochainComplex.singleFunctor C 0).obj A) K n ≃+
      ((DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) := by
  let S := (CochainComplex.singleFunctor C 0).obj A
  let e₁ := CohomologyClass.homAddEquiv (K := S) (L := K) (n := n)
  let e₂ := AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom
    (X := (HomotopyCategory.quotient C (.up ℤ)).obj S)
    (Y := (HomotopyCategory.quotient C (.up ℤ)).obj (K⟦n⟧)))
      (CochainComplex.IsKInjective.Qh_map_bijective _ (K⟦n⟧))
  let eS := (DerivedCategory.quotientCompQhIso C).app S
  let eK := (DerivedCategory.quotientCompQhIso C).app (K⟦n⟧) ≪≫
    (DerivedCategory.Q.commShiftIso n).app K
  exact e₁.trans (e₂.trans (Linear.homCongr ℤ eS eK).toAddEquiv)

def kInjectiveHomCohomologyDerivedEquiv :
    (IntegerAcyclicHomComplex.Ext.integerHomComplex A K).homology n ≃+
      ((DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :=
  (HomComplexSingleIso.Ext.integerHomCohomologyClassEquiv A K n).trans
    (kInjectiveCohomologyClassDerivedEquiv A K n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomCohomology.Ext
