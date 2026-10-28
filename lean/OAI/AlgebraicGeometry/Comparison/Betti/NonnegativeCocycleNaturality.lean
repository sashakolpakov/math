import OAI.AlgebraicGeometry.Comparison.Betti.ExtendedAcyclicCocycles
import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.HomNaturality

/-! # Nonnegative Cocycle Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeCocycleNaturality.Ext

noncomputable section

/-! The original derived class of a nonnegative cocycle commutes with
the actual extended map of complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A : C} {K L : CochainComplex C ℕ}

theorem extendedCocycle_postcomp (n : ℕ) (z : A ⟶ K.X n) (f : K ⟶ L) :
    ExtendedAcyclicCocycles.Ext.extendedCocycle A K n z ≫ (HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntGE 0)).f (n : ℤ) =
      ExtendedAcyclicCocycles.Ext.extendedCocycle A L n (z ≫ f.f n) := by
  rw [HomologicalComplex.extendMap_f f (ComplexShape.embeddingUpIntGE 0) (i := n) (by simp)]
  change (z ≫ (K.extendXIso _ _).inv) ≫ (K.extendXIso _ _).hom ≫ f.f n ≫ (L.extendXIso _ _).inv =
    (z ≫ f.f n) ≫ (L.extendXIso _ _).inv
  rw [Category.assoc, Iso.inv_hom_id_assoc, Category.assoc]

variable [HasDerivedCategory.{w} C]

theorem derivedExtendedCocycle_postcomp (n : ℕ) (z : A ⟶ K.X n)
    (hz : z ≫ K.d n (n + 1) = 0) (f : K ⟶ L) :
    ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom (ExtendedAcyclicCocycles.Ext.extendedCocycle A L n (z ≫ f.f n))
      (ExtendedAcyclicCocycles.Ext.extendedCocycle_closed A L n (z ≫ f.f n)
        (by rw [Category.assoc, f.comm, ← Category.assoc, hz, zero_comp]))) DerivedCategory.Q =
      ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom (ExtendedAcyclicCocycles.Ext.extendedCocycle A K n z)
        (ExtendedAcyclicCocycles.Ext.extendedCocycle_closed A K n z hz)) DerivedCategory.Q ≫
        (DerivedCategory.Q.map (HomologicalComplex.extendMap f
          (ComplexShape.embeddingUpIntGE 0)))⟦(n : ℤ)⟧' := by
  have h := Acyclic.HomNaturality.Ext.derivedSingleCocycle_postcomp (ExtendedAcyclicCocycles.Ext.extendedCocycle A K n z)
    (ExtendedAcyclicCocycles.Ext.extendedCocycle_closed A K n z hz) (HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntGE 0))
  simpa only [extendedCocycle_postcomp] using h

end

end OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeCocycleNaturality.Ext
