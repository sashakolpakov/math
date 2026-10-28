import OAI.AlgebraicGeometry.Comparison.Betti.ConstantSheafSections
import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionExactImage
import OAI.AlgebraicGeometry.Comparison.Betti.SingularInjective
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction

/-! # Topological Sheaf Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TopologicalSheafPullback

noncomputable section

/-!
# Actual inverse image and normalized pullback of resolutions

All functors come from the given continuous map. The constant coefficient
identifications are induced by the genuine adjunctions, and exact inverse
image carries the proved resolutions to proved resolutions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

attribute [local instance] AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits InjectiveFlasque.complexModuleLimits

variable {M N : TopCat.{0}} (f : M ⟶ N)

def sheafInverseImage : ConstantSheafSections.ComplexSheaves N ⥤ ConstantSheafSections.ComplexSheaves M :=
  TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) f

def sheafDirectImage : ConstantSheafSections.ComplexSheaves M ⥤ ConstantSheafSections.ComplexSheaves N :=
  TopCat.Sheaf.pushforward (ModuleCat.{0} ℂ) f

def sheafImageAdjunction : sheafInverseImage f ⊣ sheafDirectImage f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℂ) f

instance sheafInverseImageLeftAdjoint : (sheafInverseImage f).IsLeftAdjoint :=
  (sheafImageAdjunction f).isLeftAdjoint

instance sheafInverseImageLimits : PreservesFiniteLimits (sheafInverseImage f) :=
  Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    (Opens.map f) (ModuleCat.{0} ℂ) (Opens.grothendieckTopology N) (Opens.grothendieckTopology M)

instance sheafInverseImageColimits : PreservesFiniteColimits (sheafInverseImage f) := inferInstance

instance sheafInverseImageAdditive : (sheafInverseImage f).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (sheafInverseImage f)
  exact (sheafInverseImage f).additive_of_preservesBinaryBiproducts

instance sheafDirectImageAdditive : (sheafDirectImage f).Additive where
  map_add := by intros; rfl

instance sheafDirectImageInjectives : (sheafDirectImage f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (sheafImageAdjunction f)

def constantPullbackIso : (sheafInverseImage f).obj (ConstantSheafSections.standardConstantSheaf N) ≅
    ConstantSheafSections.standardConstantSheaf M := by
  have hT : IsTerminal ((Opens.map f).obj (⊤ : Opens N)) := by
    change IsTerminal (⊤ : Opens M)
    exact isTerminalTop
  exact (((constantSheafAdj (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ) isTerminalTop).comp
    (sheafImageAdjunction f)).leftAdjointUniq
      (constantSheafAdj (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ) hT)).app (ModuleCat.of ℂ ℂ)

def locallyConstantPullbackIso :
    (sheafInverseImage f).obj (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf N) ≅ (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M : ConstantSheafSections.ComplexSheaves M) := by
  let eN : ConstantSheafSections.standardConstantSheaf N ≅ (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf N : ConstantSheafSections.ComplexSheaves N) :=
    Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn N
  let eM : ConstantSheafSections.standardConstantSheaf M ≅ (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M : ConstantSheafSections.ComplexSheaves M) :=
    Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn M
  exact (sheafInverseImage f).mapIso eN.symm ≪≫ constantPullbackIso f ≪≫ eM

def globalSections (M : TopCat.{0}) : ConstantSheafSections.ComplexSheaves M ⥤ ModuleCat.{0} ℂ :=
  (sheafSections (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).obj (op ⊤)

instance globalSectionsAdditive (M : TopCat.{0}) : (globalSections M).Additive where
  map_add := by intros; rfl

def globalSectionPullback : globalSections N ⟶ sheafInverseImage f ⋙ globalSections M where
  app F := ((sheafImageAdjunction f).unit.app F).hom.app (op ⊤)
  naturality F G g := by
    exact congrArg (fun a => a.hom.app (op ⊤)) ((sheafImageAdjunction f).unit.naturality g)

def globalCochainPullback (K : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℕ) :
    ((globalSections N).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶
      ((globalSections M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (((sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :=
  ((globalSectionPullback f).mapHomologicalComplex (ComplexShape.up ℕ)).app K

def pulledSingularResolutionData [StronglyLocallyContractibleSpace N] :
    ResolutionExactImage.Data (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M : ConstantSheafSections.ComplexSheaves M) := by
  let R : ResolutionExactImage.Data (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf N : ConstantSheafSections.ComplexSheaves N) := SingularInjective.singularResolutionData N
  let F : ConstantSheafSections.ComplexSheaves N ⥤ ConstantSheafSections.ComplexSheaves M := sheafInverseImage f
  have : F.Additive := sheafInverseImageAdditive f
  let R' : ResolutionExactImage.Data (F.obj (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf N : ConstantSheafSections.ComplexSheaves N)) :=
    @ResolutionExactImage.exactImage _ _ _ _ _ _ _ R F
      (sheafInverseImageAdditive f) (sheafInverseImageLimits f) (sheafInverseImageColimits f)
  exact ResolutionExactImage.changeSource R' (locallyConstantPullbackIso f).symm

def pulledInjectiveResolutionData : ResolutionExactImage.Data (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M : ConstantSheafSections.ComplexSheaves M) := by
  let I : InjectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf N : ConstantSheafSections.ComplexSheaves N) := SingularInjective.singularInjectiveResolution N
  let F : ConstantSheafSections.ComplexSheaves N ⥤ ConstantSheafSections.ComplexSheaves M := sheafInverseImage f
  have : F.Additive := sheafInverseImageAdditive f
  exact ResolutionExactImage.changeSource
    (ResolutionExactImage.exactImage (C := ConstantSheafSections.ComplexSheaves N) (D := ConstantSheafSections.ComplexSheaves M)
      (ResolutionExactImage.ofInjective I) F) (locallyConstantPullbackIso f).symm

/-- Degreewise injective extension constructs the normalized map of pulled-back resolutions. -/
def injectiveResolutionPullback :
    ((sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (SingularInjective.singularInjectiveResolution N).cocomplex ⟶ (SingularInjective.singularInjectiveResolution M).cocomplex := by
  let I : InjectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M : ConstantSheafSections.ComplexSheaves M) := SingularInjective.singularInjectiveResolution M
  exact ResolutionExactImage.toInjective (pulledInjectiveResolutionData f) I

theorem injectiveResolutionPullback_normalization :
    ResolutionExactImage.cochainAugmentation (pulledInjectiveResolutionData f) ≫
        injectiveResolutionPullback f = (SingularInjective.singularInjectiveResolution M).ι :=
  ResolutionExactImage.toInjective_normalization (pulledInjectiveResolutionData f) (SingularInjective.singularInjectiveResolution M)

def injectiveSectionsPullback :
    ((globalSections N).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (SingularInjective.singularInjectiveResolution N).cocomplex ⟶
      ((globalSections M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (SingularInjective.singularInjectiveResolution M).cocomplex :=
  globalCochainPullback f (SingularInjective.singularInjectiveResolution N).cocomplex ≫
    ((globalSections M).mapHomologicalComplex (ComplexShape.up ℕ)).map (injectiveResolutionPullback f)

end

end OAI.AlgebraicGeometry.Comparison.Betti.TopologicalSheafPullback
