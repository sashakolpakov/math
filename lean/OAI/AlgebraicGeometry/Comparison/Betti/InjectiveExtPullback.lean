import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomPullback
import OAI.AlgebraicGeometry.Comparison.Betti.ExtExactFunctorNaturality

/-! # Injective Ext Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.InjectiveExtPullback

noncomputable section

/-! The actual Hom-complex pullback computes exact inverse image on Ext. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace

attribute [local instance] AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits InjectiveFlasque.complexModuleLimits

abbrev locallyConstantCoefficients (M : TopCat.{0}) : ConstantSheafSections.ComplexSheaves M := AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M

def complexInjectiveResolution (M : TopCat.{0}) : InjectiveResolution (locallyConstantCoefficients M) :=
  SingularInjective.singularInjectiveResolution M

variable {M N : TopCat.{0}} (f : M ⟶ N)

def locallyConstantExtPullback (n : ℕ)
    (a : Ext.{1} (ConstantSheafSections.standardConstantSheaf N) (locallyConstantCoefficients N) n) :
    Ext.{1} (ConstantSheafSections.standardConstantSheaf M) (locallyConstantCoefficients M) n :=
  (Ext.mk₀ (TopologicalSheafPullback.constantPullbackIso f).inv).comp
    ((a.mapExactFunctor (TopologicalSheafPullback.sheafInverseImage f)).comp (Ext.mk₀ (TopologicalSheafPullback.locallyConstantPullbackIso f).hom)
      (add_zero n)) (zero_add n)

theorem injectiveResolutionPullback_augmentation_zero :
    (TopologicalSheafPullback.sheafInverseImage f).map ((SingularInjective.singularInjectiveResolution N).ι.f 0) ≫
        (TopologicalSheafPullback.injectiveResolutionPullback f).f 0 =
      (TopologicalSheafPullback.locallyConstantPullbackIso f).hom ≫ (SingularInjective.singularInjectiveResolution M).ι.f 0 := by
  let I : InjectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf N : ConstantSheafSections.ComplexSheaves N) := SingularInjective.singularInjectiveResolution N
  let J : InjectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M : ConstantSheafSections.ComplexSheaves M) := SingularInjective.singularInjectiveResolution M
  have h := congrArg (fun k => k.f 0) (TopologicalSheafPullback.injectiveResolutionPullback_normalization f)
  change ((TopologicalSheafPullback.locallyConstantPullbackIso f).inv ≫ (TopologicalSheafPullback.sheafInverseImage f).map (I.ι.f 0)) ≫
    (TopologicalSheafPullback.injectiveResolutionPullback f).f 0 = J.ι.f 0 at h
  exact (TopologicalSheafPullback.locallyConstantPullbackIso f).inv_comp_eq.mp
    ((Category.assoc (TopologicalSheafPullback.locallyConstantPullbackIso f).inv ((TopologicalSheafPullback.sheafInverseImage f).map (I.ι.f 0))
      ((TopologicalSheafPullback.injectiveResolutionPullback f).f 0)).symm.trans h)

theorem locallyConstantExtPullback_extMk (n : ℕ)
    (g : (InjectiveHomPullback.injectiveHomSectionsComplex N).X n)
    (hg : (InjectiveHomPullback.injectiveHomSectionsComplex N).d n (n + 1) g = 0) :
    locallyConstantExtPullback f n (InjectiveResolution.extMk.{1} (C := ConstantSheafSections.ComplexSheaves N)
      (complexInjectiveResolution N) g (n + 1) rfl hg) =
      InjectiveResolution.extMk.{1} (C := ConstantSheafSections.ComplexSheaves M) (complexInjectiveResolution M)
        ((InjectiveHomPullback.injectiveHomSectionsPullback f).f n g) (n + 1) rfl
        (CochainClasses.Homology.cochain_map_closed (InjectiveHomPullback.injectiveHomSectionsPullback f) n g hg) := by
  let I := complexInjectiveResolution N
  let J := complexInjectiveResolution M
  let F : ConstantSheafSections.ComplexSheaves N ⥤ ConstantSheafSections.ComplexSheaves M := TopologicalSheafPullback.sheafInverseImage f
  let φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex :=
    TopologicalSheafPullback.injectiveResolutionPullback f
  have hφ : F.map (I.ι.f 0) ≫ φ.f 0 = (TopologicalSheafPullback.locallyConstantPullbackIso f).hom ≫ J.ι.f 0 :=
    injectiveResolutionPullback_augmentation_zero f
  have hF := ExtExactFunctorNaturality.mapExactFunctor_extMk.{1, 1} (C := ConstantSheafSections.ComplexSheaves N) (D := ConstantSheafSections.ComplexSheaves M)
    F I J φ (TopologicalSheafPullback.locallyConstantPullbackIso f).hom hφ g hg
  have hp := InjectiveResolution.mk₀_comp_extMk.{1} (C := ConstantSheafSections.ComplexSheaves M) J (F.map g ≫ φ.f n) (n + 1) rfl
    (ExtExactFunctorNaturality.resolutionMapCocycle_closed F I J φ g hg) (TopologicalSheafPullback.constantPullbackIso f).inv
  change (Ext.mk₀ (TopologicalSheafPullback.constantPullbackIso f).inv).comp
    (((InjectiveResolution.extMk.{1} (C := ConstantSheafSections.ComplexSheaves N) I g (n + 1) rfl hg).mapExactFunctor F).comp
      (Ext.mk₀ (TopologicalSheafPullback.locallyConstantPullbackIso f).hom) (add_zero n)) (zero_add n) = _
  rw [hF]
  refine hp.trans ?_
  congr 1
  exact (Category.assoc _ _ _).symm.trans (InjectiveHomPullback.injectiveHomSectionsPullback_f f n g).symm

def injectiveHomologyExtEquiv (M : TopCat.{0}) (n : ℕ) :
    (InjectiveHomPullback.injectiveHomSectionsComplex M).homology n ≃ₗ[ℂ]
      Ext.{1} (ConstantSheafSections.standardConstantSheaf M) (locallyConstantCoefficients M) n :=
  InjectiveHomologyExt.homologyExtLinearEquiv (C := ConstantSheafSections.ComplexSheaves M) (R := ℂ) (complexInjectiveResolution M) n

theorem injectiveHomologyExtEquiv_class (M : TopCat.{0}) (n : ℕ)
    (g : (InjectiveHomPullback.injectiveHomSectionsComplex M).X n)
    (hg : (InjectiveHomPullback.injectiveHomSectionsComplex M).d n (n + 1) g = 0) :
    injectiveHomologyExtEquiv M n (CochainClasses.Homology.cochainClass (InjectiveHomPullback.injectiveHomSectionsComplex M) n g hg) =
      InjectiveResolution.extMk.{1} (C := ConstantSheafSections.ComplexSheaves M) (complexInjectiveResolution M)
        g (n + 1) rfl hg :=
  HomologyExtNaturality.homologyExtLinearEquiv_class (C := ConstantSheafSections.ComplexSheaves M) (R := ℂ)
    (complexInjectiveResolution M) n g hg

theorem injectiveHomologyExtEquiv_pullback (n : ℕ) (a : (InjectiveHomPullback.injectiveHomSectionsComplex N).homology n) :
    injectiveHomologyExtEquiv M n
        (HomologicalComplex.homologyMap (InjectiveHomPullback.injectiveHomSectionsPullback f) n a) =
      locallyConstantExtPullback f n (injectiveHomologyExtEquiv N n a) := by
  obtain ⟨g, hg, rfl⟩ := CochainClasses.Homology.cochainClass_surjective (InjectiveHomPullback.injectiveHomSectionsComplex N) n a
  rw [CochainClasses.Homology.cochainClass_naturality (InjectiveHomPullback.injectiveHomSectionsPullback f) n g hg,
    injectiveHomologyExtEquiv_class M n, injectiveHomologyExtEquiv_class N n]
  exact (locallyConstantExtPullback_extMk f n g hg).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.InjectiveExtPullback
