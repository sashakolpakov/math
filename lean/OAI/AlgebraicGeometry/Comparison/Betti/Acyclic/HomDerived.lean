import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.InjectiveReplacement
import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomCohomology

/-! # Hom Derived -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.HomDerived.Ext

noncomputable section

/-! Cohomology of Hom computes hypercohomology for bounded-below complexes of Ext-acyclic terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian

universe u v w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] [HasDerivedCategory.{w'} C]
  (A : C) (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyGE b]

def acyclicHomCohomologyDerivedEquiv
    (hExt : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1))) (n : ℤ) :
    (IntegerAcyclicHomComplex.Ext.integerHomComplex A K).homology n ≃+
      ((DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) := by
  let I := InjectiveReplacement.Ext.boundedInjectiveReplacement K b
  let e₁ := (InjectiveReplacement.Ext.boundedInjectiveReplacementHomologyIso K b A hExt n).addCommGroupIsoToAddEquiv
  let e₂ := InjectiveHomCohomology.Ext.kInjectiveHomCohomologyDerivedEquiv A I n
  have : IsIso (DerivedCategory.Q.map (InjectiveReplacement.Ext.boundedInjectiveReplacementMap K b)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C _).mpr inferInstance
  let e := (shiftFunctor (DerivedCategory C) n).mapIso
    (asIso (DerivedCategory.Q.map (InjectiveReplacement.Ext.boundedInjectiveReplacementMap K b))).symm
  exact e₁.trans (e₂.trans (Linear.homCongr ℤ (Iso.refl _) e).toAddEquiv)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.HomDerived.Ext
