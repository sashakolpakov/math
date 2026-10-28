import OAI.AlgebraicGeometry.Comparison.Betti.LinearHomForget
import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.HomNaturality
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # Linear Hom Derived -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext

noncomputable section

/-! The acyclic-complex hypercohomology calculation preserves the original scalar action. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian

universe u v w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] [HasDerivedCategory.{w'} C]
  {R : Type v} [CommRing R] [Linear R C]
  (A : C) (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyGE b]

def acyclicLinearHomCohomologyDerivedEquiv
    (hExt : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1))) (n : ℤ) :
    (LinearHomForget.Ext.integerLinearHomComplex (R := R) A K).homology n ≃ₗ[R]
      ((DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) where
  toAddEquiv := (LinearHomForget.Ext.integerLinearHomologyForgetEquiv (R := R) A K n).trans
    (HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A K b hExt n)
  map_smul' r a := by
    let E := HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A K b hExt n
    let e := LinearHomForget.Ext.integerLinearHomologyForgetEquiv (R := R) A K n
    change E (e (r • a)) = r • E (e a)
    have h₁ := congrArg E (LinearHomForget.Ext.integerLinearHomologyForgetEquiv_smul A K n r a)
    have h₂ := HomNaturality.Ext.acyclicHomCohomologyDerivedEquiv_naturality A K K b b hExt hExt
      (r • 𝟙 K) n (e a)
    have h₃ : E (e a) ≫ (DerivedCategory.Q.map (r • 𝟙 K))⟦n⟧' = r • E (e a) := by
      simp only [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id,
        Linear.comp_smul, Category.comp_id]
    exact h₁.trans (h₂.trans h₃)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived.Ext
