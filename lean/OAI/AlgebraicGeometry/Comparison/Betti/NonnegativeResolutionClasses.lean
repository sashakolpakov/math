import OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeExtensionNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeCocycleNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.ExtCocycleNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionCocycleNaturality

/-! # Nonnegative Resolution Classes -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeResolutionClasses.Ext

noncomputable section

/-! A normalized comparison of an actual nonnegative resolution with an
injective resolution preserves the original derived cocycle class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A Z : C} {K L : CochainComplex C ℕ}

open OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeExtensionNormalization.Complex

theorem extendAugmentation_postcomp (a : (CochainComplex.single₀ C).obj Z ⟶ K)
    (f : K ⟶ L) :
    AugmentationExtension.Complex.extendAugmentation a ≫ HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntGE 0) =
      AugmentationExtension.Complex.extendAugmentation (a ≫ f) := by
  unfold AugmentationExtension.Complex.extendAugmentation
  erw [Category.assoc, ← HomologicalComplex.extendMap_comp]

instance extendAugmentation_quasiIso (a : (CochainComplex.single₀ C).obj Z ⟶ K)
    [QuasiIso a] : QuasiIso (AugmentationExtension.Complex.extendAugmentation a) := by
  have h : QuasiIso (HomologicalComplex.extendMap a (ComplexShape.embeddingUpIntGE 0)) :=
    (HomologicalComplex.quasiIso_extendMap_iff a (ComplexShape.embeddingUpIntGE 0)).2 inferInstance
  let e := HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntGE 0) Z 0 0 (by simp)
  have he : QuasiIso e.inv := inferInstance
  exact quasiIso_comp e.inv _ (hφ := he) (hφ' := h)

variable [HasDerivedCategory.{w} C] [HasExt.{w} C]

omit [HasExt C] in
theorem resolutionCocycleHom_congr {Y : C} {D : CochainComplex C ℤ} {q : ℤ}
    (a : (CochainComplex.singleFunctor C 0).obj Y ⟶ D) [QuasiIso a]
    {z z' : A ⟶ D.X q} {hz : z ≫ D.d q (q + 1) = 0}
    {hz' : z' ≫ D.d q (q + 1) = 0} (h : z = z') :
    ResolutionCocycleClass.Ext.resolutionCocycleHom a z hz = ResolutionCocycleClass.Ext.resolutionCocycleHom a z' hz' := by
  subst z'
  rfl

theorem normalizedResolution_extMk_hom
    (a : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso a]
    (I : InjectiveResolution Z) (f : K ⟶ I.cocomplex) (h : a ≫ f = I.ι)
    (n : ℕ) (z : A ⟶ K.X n) (hz : z ≫ K.d n (n + 1) = 0) :
    (I.extMk (z ≫ f.f n) (n + 1) rfl
      (by rw [Category.assoc, f.comm, ← Category.assoc, hz, zero_comp])).hom =
      ResolutionCocycleClass.Ext.resolutionCocycleHom (AugmentationExtension.Complex.extendAugmentation a)
        (ExtendedAcyclicCocycles.Ext.extendedCocycle A K n z) (ExtendedAcyclicCocycles.Ext.extendedCocycle_closed A K n z hz) := by
  let g := HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntGE 0) ≫
    (NonnegativeExtensionNormalization.Complex.nonnegativeExtensionIso I.cocomplex).hom
  have hn : AugmentationExtension.Complex.extendAugmentation a ≫ g =
      (CochainComplex.singleFunctor C 0).map (𝟙 Z) ≫ I.ι' := by
    dsimp only [g]
    erw [← Category.assoc, extendAugmentation_postcomp, h,
      NonnegativeExtensionNormalization.Complex.nonnegativeExtensionIso_injective_augmentation, CategoryTheory.Functor.map_id, Category.id_comp]
  have hg : ExtendedAcyclicCocycles.Ext.extendedCocycle A K n z ≫ g.f (n : ℤ) =
      (z ≫ f.f n) ≫ (I.cochainComplexXIso n n rfl).inv := by
    change ExtendedAcyclicCocycles.Ext.extendedCocycle A K n z ≫
      ((HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntGE 0)).f (n : ℤ) ≫
        (NonnegativeExtensionNormalization.Complex.nonnegativeExtensionIso I.cocomplex).hom.f (n : ℤ)) = _
    rw [← Category.assoc, NonnegativeCocycleNaturality.Ext.extendedCocycle_postcomp]
    unfold ExtendedAcyclicCocycles.Ext.extendedCocycle
    rw [Category.assoc, NonnegativeExtensionNormalization.Complex.nonnegativeExtensionIso_cocycle]
    rfl
  have hc := ResolutionCocycleNaturality.Ext.resolutionCocycleHom_postcomp (AugmentationExtension.Complex.extendAugmentation a) I.ι' g (𝟙 Z) hn
    (ExtendedAcyclicCocycles.Ext.extendedCocycle A K n z) (ExtendedAcyclicCocycles.Ext.extendedCocycle_closed A K n z hz)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  rw [ExtCocycleNormalization.extMk_hom_resolutionCocycleHom]
  exact (resolutionCocycleHom_congr I.ι' hg.symm).trans hc

end

end OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeResolutionClasses.Ext
