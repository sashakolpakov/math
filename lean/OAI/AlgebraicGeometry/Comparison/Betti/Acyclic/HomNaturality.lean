import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.CocycleNormalization

/-! # Hom Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.HomNaturality.Ext

noncomputable section

/-! The acyclic-complex calculation is natural for actual maps of complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian Opposite

universe u v w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w'} C]

theorem derivedSingleCocycle_postcomp {A : C} {K L : CochainComplex C ℤ} {n : ℤ}
    (z : A ⟶ K.X n) (hz : z ≫ K.d n (n + 1) = 0) (f : K ⟶ L) :
    ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom (z ≫ f.f n)
      (by rw [Category.assoc, f.comm, ← Category.assoc, hz, zero_comp])) DerivedCategory.Q =
    ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom z hz) DerivedCategory.Q ≫
      (DerivedCategory.Q.map f)⟦n⟧' := by
  rw [ResolutionCocycleNaturality.Ext.singleCocycleHom_postcomp]
  have h := ShiftedHom.map_comp (SingleCocycleFunctor.Ext.singleCocycleHom z hz)
    (ShiftedHom.mk₀ (0 : ℤ) rfl f) (zero_add n) DerivedCategory.Q
  simpa only [ShiftedHom.comp_mk₀, ShiftedHom.map_mk₀] using h

variable [EnoughInjectives C] [HasExt.{w} C] (A : C)
  (K L : CochainComplex C ℤ) (b c : ℤ) [K.IsStrictlyGE b] [L.IsStrictlyGE c]

theorem acyclicHomCohomologyDerivedEquiv_naturality
    (hK : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext A (L.X p) (q + 1)))
    (f : K ⟶ L) (n : ℤ) (a : (IntegerAcyclicHomComplex.Ext.integerHomComplex A K).homology n) :
    HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A L c hL n
      (HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map f) n a) =
      HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A K b hK n a ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  obtain ⟨z, hz, rfl⟩ := AbCochainClasses.Homology.cochainClass_surjective (IntegerAcyclicHomComplex.Ext.integerHomComplex A K) n a
  change A ⟶ K.X n at z
  change z ≫ K.d n (n + 1) = 0 at hz
  let H : IntegerAcyclicHomComplex.Ext.integerHomComplex A K ⟶ IntegerAcyclicHomComplex.Ext.integerHomComplex A L :=
    ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map f
  have hz' : (z ≫ f.f n) ≫ L.d n (n + 1) = 0 := by
    rw [Category.assoc, f.comm, ← Category.assoc, hz, zero_comp]
  have h₁ := congrArg (HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A L c hL n)
    (AbCochainClasses.Homology.cochainClass_naturality n H z hz)
  have h₂ := CocycleNormalization.Ext.acyclicHomCohomologyDerivedEquiv_class A L c hL n (z ≫ f.f n) hz'
  have h₃ := derivedSingleCocycle_postcomp z hz f
  have h₄ := congrArg (fun g => g ≫ (DerivedCategory.Q.map f)⟦n⟧')
    (CocycleNormalization.Ext.acyclicHomCohomologyDerivedEquiv_class A K b hK n z hz).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.HomNaturality.Ext
