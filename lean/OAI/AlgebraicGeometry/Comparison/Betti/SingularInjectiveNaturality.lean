import OAI.AlgebraicGeometry.Comparison.Betti.SingularAugmentationNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.SingularGlobalNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionUniqueness

/-! # Singular Injective Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SingularInjectiveNaturality

noncomputable section

/-! Naturality of the constructed singular-to-injective comparison, up to homotopy. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

attribute [local instance] AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits InjectiveFlasque.complexModuleLimits

variable {M N : TopCat.{0}} (f : M ⟶ N)
  [StronglyLocallyContractibleSpace M] [StronglyLocallyContractibleSpace N]

omit [StronglyLocallyContractibleSpace M] in
theorem pulledSingularToInjective_augmentation :
    ResolutionExactImage.cochainAugmentation (TopologicalSheafPullback.pulledSingularResolutionData f) ≫
      ((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (SingularInjective.singularSheafToInjective N) =
      ResolutionExactImage.cochainAugmentation (TopologicalSheafPullback.pulledInjectiveResolutionData f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    have h : AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation N ≫
        (SingularInjective.singularSheafToInjective N).f 0 = (SingularInjective.singularInjectiveResolution N).ι.f 0 :=
      congrArg (fun k => k.f 0) (SingularInjective.singularSheafToInjective_normalization N)
    change ((TopologicalSheafPullback.locallyConstantPullbackIso f).inv ≫
      (TopologicalSheafPullback.sheafInverseImage f).map (AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation N)) ≫
        (TopologicalSheafPullback.sheafInverseImage f).map ((SingularInjective.singularSheafToInjective N).f 0) =
      (TopologicalSheafPullback.locallyConstantPullbackIso f).inv ≫
        (TopologicalSheafPullback.sheafInverseImage f).map ((SingularInjective.singularInjectiveResolution N).ι.f 0)
    erw [Category.assoc, ← Functor.map_comp, h]
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
      (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M : ConstantSheafSections.ComplexSheaves M) (n + 1) (by omega)).eq_of_src _ _

def singularInjectivePullbackHomotopy :
    Homotopy
      (((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (SingularInjective.singularSheafToInjective N) ≫ TopologicalSheafPullback.injectiveResolutionPullback f)
      (SingularGlobalNaturality.singularSheafPullback f ≫ SingularInjective.singularSheafToInjective M) := by
  let I : InjectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M : ConstantSheafSections.ComplexSheaves M) := SingularInjective.singularInjectiveResolution M
  apply ResolutionUniqueness.comparisonHomotopy (TopologicalSheafPullback.pulledSingularResolutionData f) I.cocomplex
  erw [← Category.assoc, pulledSingularToInjective_augmentation,
    TopologicalSheafPullback.injectiveResolutionPullback_normalization, ← Category.assoc,
    SingularAugmentationNaturality.singularSheafPullback_resolution, SingularInjective.singularSheafToInjective_normalization]

omit [StronglyLocallyContractibleSpace M] [StronglyLocallyContractibleSpace N] in
theorem globalCochainPullback_naturality
    {K L : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℕ} (g : K ⟶ L) :
    ((TopologicalSheafPullback.globalSections N).mapHomologicalComplex (ComplexShape.up ℕ)).map g ≫
        TopologicalSheafPullback.globalCochainPullback f L =
      TopologicalSheafPullback.globalCochainPullback f K ≫
        ((TopologicalSheafPullback.globalSections M).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map g) :=
  ((TopologicalSheafPullback.globalSectionPullback f).mapHomologicalComplex (ComplexShape.up ℕ)).naturality g

def singularToInjectiveSectionsPullbackHomotopy :
    Homotopy
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f ≫ SingularInjective.singularToInjectiveSections M)
      (SingularInjective.singularToInjectiveSections N ≫ TopologicalSheafPullback.injectiveSectionsPullback f) := by
  let G := (TopologicalSheafPullback.globalSections M).mapHomologicalComplex (ComplexShape.up ℕ)
  let p := AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℂ ℂ) N ≫
    TopologicalSheafPullback.globalCochainPullback f (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex N)
  have hL : AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f ≫ SingularInjective.singularToInjectiveSections M =
      p ≫ G.map (SingularGlobalNaturality.singularSheafPullback f ≫ SingularInjective.singularSheafToInjective M) := by
    change AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f ≫
      (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℂ ℂ) M ≫ G.map (SingularInjective.singularSheafToInjective M)) = _
    erw [← Category.assoc, SingularGlobalNaturality.singularCochainsToSheafSections_pullback_naturality]
    erw [G.map_comp (SingularGlobalNaturality.singularSheafPullback f) (SingularInjective.singularSheafToInjective M)]
    rfl
  have hR : SingularInjective.singularToInjectiveSections N ≫ TopologicalSheafPullback.injectiveSectionsPullback f =
      p ≫ G.map (((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (SingularInjective.singularSheafToInjective N) ≫ TopologicalSheafPullback.injectiveResolutionPullback f) := by
    change (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℂ ℂ) N ≫
      ((TopologicalSheafPullback.globalSections N).mapHomologicalComplex (ComplexShape.up ℕ)).map (SingularInjective.singularSheafToInjective N)) ≫
        (TopologicalSheafPullback.globalCochainPullback f (SingularInjective.singularInjectiveResolution N).cocomplex ≫
          G.map (TopologicalSheafPullback.injectiveResolutionPullback f)) = _
    erw [Category.assoc, ← Category.assoc
      (((TopologicalSheafPullback.globalSections N).mapHomologicalComplex (ComplexShape.up ℕ)).map (SingularInjective.singularSheafToInjective N)),
      globalCochainPullback_naturality]
    erw [G.map_comp
      (((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (SingularInjective.singularSheafToInjective N)) (TopologicalSheafPullback.injectiveResolutionPullback f)]
    rfl
  exact (Homotopy.ofEq hL).trans
    ((((TopologicalSheafPullback.globalSections M).mapHomotopy (singularInjectivePullbackHomotopy f)).symm.compLeft p).trans
      (Homotopy.ofEq hR.symm))

theorem singularToInjectiveSections_homology_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f) n ≫
        HomologicalComplex.homologyMap (SingularInjective.singularToInjectiveSections M) n =
      HomologicalComplex.homologyMap (SingularInjective.singularToInjectiveSections N) n ≫
        HomologicalComplex.homologyMap (TopologicalSheafPullback.injectiveSectionsPullback f) n := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (ComplexShape.up ℕ) n
  exact (H.map_comp (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f) (SingularInjective.singularToInjectiveSections M)).symm.trans
    (((singularToInjectiveSectionsPullbackHomotopy f).homologyMap_eq n).trans
      (H.map_comp (SingularInjective.singularToInjectiveSections N) (TopologicalSheafPullback.injectiveSectionsPullback f)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.SingularInjectiveNaturality
