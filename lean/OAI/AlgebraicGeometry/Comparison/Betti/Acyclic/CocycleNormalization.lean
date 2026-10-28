import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.HomDerived
import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveCocycleNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionCocycleNaturality

/-! # Cocycle Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.CocycleNormalization.Ext

noncomputable section

/-! The acyclic-complex calculation sends every cocycle to its original derived class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian Opposite _root_.CochainComplex.HomComplex

universe u v w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] [HasDerivedCategory.{w'} C]
  (A : C) (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyGE b]

theorem acyclicHomCohomologyDerivedEquiv_class
    (hExt : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1))) (n : ℤ)
    (f : A ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A K b hExt n
      (AbCochainClasses.Homology.cochainClass (IntegerAcyclicHomComplex.Ext.integerHomComplex A K) n f hf) =
        ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom f hf) DerivedCategory.Q := by
  let I := InjectiveReplacement.Ext.boundedInjectiveReplacement K b
  let j := InjectiveReplacement.Ext.boundedInjectiveReplacementMap K b
  let H : IntegerAcyclicHomComplex.Ext.integerHomComplex A K ⟶ IntegerAcyclicHomComplex.Ext.integerHomComplex A I :=
    ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map j
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  have : IsIso (Q.map j) := (DerivedCategory.isIso_Q_map_iff_quasiIso C j).mpr inferInstance
  have hf' : (f ≫ j.f n) ≫ I.d n (n + 1) = 0 := by
    rw [Category.assoc, j.comm, ← Category.assoc, hf, zero_comp]
  have hc : InjectiveHomCohomology.Ext.kInjectiveHomCohomologyDerivedEquiv A I n
      (HomologicalComplex.homologyMap H n
        (AbCochainClasses.Homology.cochainClass (IntegerAcyclicHomComplex.Ext.integerHomComplex A K) n f hf)) =
      ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom (f ≫ j.f n) hf') Q :=
    (congrArg (InjectiveHomCohomology.Ext.kInjectiveHomCohomologyDerivedEquiv A I n)
      (AbCochainClasses.Homology.cochainClass_naturality n H f hf)).trans
        (InjectiveCocycleNormalization.Ext.kInjectiveHomCohomologyDerivedEquiv_class A I n (f ≫ j.f n) hf')
  have hp : ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom (f ≫ j.f n) hf') Q =
      ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom f hf) Q ≫ (Q.map j)⟦n⟧' := by
    rw [ResolutionCocycleNaturality.Ext.singleCocycleHom_postcomp]
    have h := ShiftedHom.map_comp (SingleCocycleFunctor.Ext.singleCocycleHom f hf)
      (ShiftedHom.mk₀ (0 : ℤ) rfl j) (zero_add n) Q
    simpa only [ShiftedHom.comp_mk₀, ShiftedHom.map_mk₀] using h
  change (𝟙 _ ≫ InjectiveHomCohomology.Ext.kInjectiveHomCohomologyDerivedEquiv A I n
    (HomologicalComplex.homologyMap H n
      (AbCochainClasses.Homology.cochainClass (IntegerAcyclicHomComplex.Ext.integerHomComplex A K) n f hf))) ≫
      (inv (Q.map j))⟦n⟧' = _
  rw [Category.id_comp, hc, hp]
  erw [Category.assoc, ← Functor.map_comp,
    IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.CocycleNormalization.Ext
