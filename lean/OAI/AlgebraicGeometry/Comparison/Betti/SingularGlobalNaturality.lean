import OAI.AlgebraicGeometry.Comparison.Betti.TopologicalSheafPullback
import OAI.AlgebraicGeometry.Comparison.Betti.SingularPresheafPullback

/-! # Singular Global Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SingularGlobalNaturality

noncomputable section

section

/-!
# Pullback of the actual singular-cochain sheaf complex

The degreewise singular pullbacks descend through the genuine
sheafification adjunction, then the actual inverse-image adjunction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

attribute [local instance] AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits InjectiveFlasque.complexModuleLimits

def sheafificationCochainAdjunction (M : TopCat.{0}) :
    (presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ) ⊣
      (sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ) :=
  Complex.Adjunction.onComplexes
    (sheafificationAdjunction (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)) (ComplexShape.up ℕ)

variable {M N : TopCat.{0}} (f : M ⟶ N)

def sheafImageCochainAdjunction :
    (TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ) ⊣
      (TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (ComplexShape.up ℕ) :=
  Complex.Adjunction.onComplexes (TopologicalSheafPullback.sheafImageAdjunction f) (ComplexShape.up ℕ)

def singularPresheafToDirectImageSheaf : AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) N ⟶
    ((sheafToPresheaf (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
      (((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex M)) :=
  SingularPresheafPullback.singularPresheafPullback f ≫
    ((SingularPresheafPullback.preimagePresheafFunctor f).mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((sheafificationCochainAdjunction M).unit.app (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) M))

def singularSheafDirectImage : AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex N ⟶
    ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex M) :=
  ((sheafificationCochainAdjunction N).homEquiv (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) N)
    (((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex M))).symm (singularPresheafToDirectImageSheaf f)

def singularSheafPullback :
    ((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex N) ⟶
      AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex M :=
  ((sheafImageCochainAdjunction f).homEquiv (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex N)
    (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex M)).symm (singularSheafDirectImage f)

theorem singularSheafDirectImage_normalization :
    (sheafificationCochainAdjunction N).homEquiv _ _ (singularSheafDirectImage f) =
      singularPresheafToDirectImageSheaf f :=
  (sheafificationCochainAdjunction N).homEquiv _ _ |>.apply_symm_apply _

theorem singularSheafPullback_normalization :
    (sheafImageCochainAdjunction f).homEquiv _ _ (singularSheafPullback f) =
      singularSheafDirectImage f :=
  (sheafImageCochainAdjunction f).homEquiv _ _ |>.apply_symm_apply _

theorem singularSheafDirectImage_unit (n : ℕ) (U : Opens N) :
    (CategoryTheory.toSheafify (Opens.grothendieckTopology N)
        (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℂ ℂ) N n)).app (op U) ≫
      ((singularSheafDirectImage f).f n).hom.app (op U) =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (SingularPresheafPullback.openPreimageMap f U)).f n ≫
      (CategoryTheory.toSheafify (Opens.grothendieckTopology M)
        (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℂ ℂ) M n)).app (op ((Opens.map f).obj U)) := by
  have h := singularSheafDirectImage_normalization f
  erw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k => (k.f n).app (op U)) h

theorem singularSheafPullback_sections :
    TopologicalSheafPullback.globalCochainPullback f (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex N) ≫
        ((TopologicalSheafPullback.globalSections M).mapHomologicalComplex (ComplexShape.up ℕ)).map (singularSheafPullback f) =
      ((TopologicalSheafPullback.globalSections N).mapHomologicalComplex (ComplexShape.up ℕ)).map (singularSheafDirectImage f) := by
  have h := singularSheafPullback_normalization f
  rw [Adjunction.homEquiv_unit] at h
  have hm := ((TopologicalSheafPullback.globalSections N).mapHomologicalComplex (ComplexShape.up ℕ)).congr_map h
  rw [Functor.map_comp] at hm
  exact hm

end

/-! The original global singular-cochain sheafification map is natural for continuous maps. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {M N : TopCat.{0}} (f : M ⟶ N)

theorem singularCochainsToSheafSections_direct_naturality :
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f ≫ AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℂ ℂ) M =
      AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℂ ℂ) N ≫
        ((TopologicalSheafPullback.globalSections N).mapHomologicalComplex (ComplexShape.up ℕ)).map (singularSheafDirectImage f) := by
  let iM : TopCat.of (⊤ : Opens M) ⟶ M := Opens.inclusion' ⊤
  let iN : TopCat.of (⊤ : Opens N) ⟶ N := Opens.inclusion' ⊤
  have he : iM ≫ f = SingularPresheafPullback.openPreimageMap f ⊤ ≫ iN := by ext p; rfl
  have hp : AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f ≫ AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) iM =
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) iN ≫
        AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (SingularPresheafPullback.openPreimageMap f ⊤) :=
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp (ModuleCat.of ℂ ℂ) iM f).symm.trans
      ((congrArg (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ)) he).trans
        (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp (ModuleCat.of ℂ ℂ) (SingularPresheafPullback.openPreimageMap f ⊤) iN))
  apply HomologicalComplex.Hom.ext
  funext n
  let uM := (CategoryTheory.toSheafify (Opens.grothendieckTopology M)
    (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℂ ℂ) M n)).app (Opposite.op ⊤)
  let uN := (CategoryTheory.toSheafify (Opens.grothendieckTopology N)
    (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℂ ℂ) N n)).app (Opposite.op ⊤)
  let s := ((singularSheafDirectImage f).f n).hom.app (Opposite.op ⊤)
  have hpn : (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f).f n ≫
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) iM).f n =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) iN).f n ≫
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (SingularPresheafPullback.openPreimageMap f ⊤)).f n :=
    congrArg (fun k => k.f n) hp
  have hu : uN ≫ s =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (SingularPresheafPullback.openPreimageMap f ⊤)).f n ≫ uM :=
    singularSheafDirectImage_unit f n ⊤
  change (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f).f n ≫
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) iM).f n ≫ uM) =
    ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) iN).f n ≫ uN) ≫ s
  erw [← Category.assoc, hpn, Category.assoc, ← hu, ← Category.assoc]

theorem singularCochainsToSheafSections_pullback_naturality :
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f ≫ AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℂ ℂ) M =
      AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℂ ℂ) N ≫
        TopologicalSheafPullback.globalCochainPullback f (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex N) ≫
          ((TopologicalSheafPullback.globalSections M).mapHomologicalComplex (ComplexShape.up ℕ)).map (singularSheafPullback f) := by
  erw [singularSheafPullback_sections]
  exact singularCochainsToSheafSections_direct_naturality f

end

end OAI.AlgebraicGeometry.Comparison.Betti.SingularGlobalNaturality
