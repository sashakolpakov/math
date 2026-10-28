import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.CocycleNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionCocycleNaturality

/-! # Acyclic Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AcyclicCoefficient.AcyclicCoefficientNaturality

noncomputable section

/-! The native acyclic comparison is natural in the coefficient object as well as the complex. -/

open _root_.CategoryTheory Limits Abelian Opposite

universe u v w z

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasDerivedCategory.{z} C]
  {A B : C} (v : A ⟶ B) (K : CochainComplex C ℤ)

def complexMap : AlgebraicGeometry.Comparison.Betti.IntegerAcyclicHomComplex.Ext.integerHomComplex B K ⟶ AlgebraicGeometry.Comparison.Betti.IntegerAcyclicHomComplex.Ext.integerHomComplex A K :=
  ((preadditiveCoyoneda.map v.op).mapHomologicalComplex (.up ℤ)).app K

omit [HasExt C] in
theorem derivedClass (n : ℤ) (a : B ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    ShiftedHom.map (AlgebraicGeometry.Comparison.Betti.SingleCocycleFunctor.Ext.singleCocycleHom (v ≫ a) (by rw [Category.assoc, ha, comp_zero])) DerivedCategory.Q =
      (DerivedCategory.singleFunctor C 0).map v ≫ ShiftedHom.map (AlgebraicGeometry.Comparison.Betti.SingleCocycleFunctor.Ext.singleCocycleHom a ha) DerivedCategory.Q := by
  have hs := congrArg (fun k : (CochainComplex.singleFunctor C 0).obj A ⟶ K⟦n⟧ =>
    ShiftedHom.map k DerivedCategory.Q) (AlgebraicGeometry.Comparison.Betti.ResolutionCocycleNaturality.Ext.singleCocycleHom_precomp v a ha)
  have hm : ShiftedHom.map ((CochainComplex.singleFunctor C 0).map v ≫ AlgebraicGeometry.Comparison.Betti.SingleCocycleFunctor.Ext.singleCocycleHom a ha)
      DerivedCategory.Q = DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map v) ≫
        ShiftedHom.map (AlgebraicGeometry.Comparison.Betti.SingleCocycleFunctor.Ext.singleCocycleHom a ha) DerivedCategory.Q := by
    simpa only [ShiftedHom.mk₀_comp, ShiftedHom.map_mk₀] using
      ShiftedHom.map_comp (ShiftedHom.mk₀ (0 : ℤ) rfl ((CochainComplex.singleFunctor C 0).map v))
        (AlgebraicGeometry.Comparison.Betti.SingleCocycleFunctor.Ext.singleCocycleHom a ha) (add_zero n) DerivedCategory.Q
  exact hs.trans hm

variable [EnoughInjectives C]

theorem naturality (b : ℤ) [K.IsStrictlyGE b]
    (hA : ∀ p q, Subsingleton (Ext.{w} A (K.X p) (q + 1)))
    (hB : ∀ p q, Subsingleton (Ext.{w} B (K.X p) (q + 1)))
    (n : ℤ) (x : (AlgebraicGeometry.Comparison.Betti.IntegerAcyclicHomComplex.Ext.integerHomComplex B K).homology n) :
    AlgebraicGeometry.Comparison.Betti.Acyclic.HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A K b hA n
      (HomologicalComplex.homologyMap (complexMap v K) n x) =
      (DerivedCategory.singleFunctor C 0).map v ≫ AlgebraicGeometry.Comparison.Betti.Acyclic.HomDerived.Ext.acyclicHomCohomologyDerivedEquiv B K b hB n x := by
  obtain ⟨a, ha, rfl⟩ := AlgebraicGeometry.Comparison.Betti.AbCochainClasses.Homology.cochainClass_surjective (AlgebraicGeometry.Comparison.Betti.IntegerAcyclicHomComplex.Ext.integerHomComplex B K) n x
  change B ⟶ K.X n at a
  change a ≫ K.d n (n + 1) = 0 at ha
  have h₁ := congrArg (AlgebraicGeometry.Comparison.Betti.Acyclic.HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A K b hA n)
    (AlgebraicGeometry.Comparison.Betti.AbCochainClasses.Homology.cochainClass_naturality n (complexMap v K) a ha)
  have h₂ := AlgebraicGeometry.Comparison.Betti.Acyclic.CocycleNormalization.Ext.acyclicHomCohomologyDerivedEquiv_class A K b hA n (v ≫ a)
    (AlgebraicGeometry.Comparison.Betti.AbCochainClasses.Homology.map_closed n (complexMap v K) a ha)
  have h₃ := derivedClass v K n a ha
  have h₄ := congrArg (fun k => (DerivedCategory.singleFunctor C 0).map v ≫ k)
    (AlgebraicGeometry.Comparison.Betti.Acyclic.CocycleNormalization.Ext.acyclicHomCohomologyDerivedEquiv_class B K b hB n a ha).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AcyclicCoefficient.AcyclicCoefficientNaturality
