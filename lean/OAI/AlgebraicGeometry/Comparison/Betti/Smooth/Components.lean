import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveComponent
import OAI.AlgebraicTopology.Cohomology.Singular.FiniteCoproduct
import OAI.AlgebraicGeometry.Betti.Scheme

/-! # Components -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Components

noncomputable section

/-!
# Integral components of arbitrary smooth finite-type complex schemes

Smoothness gives domain stalks. Noetherianity makes the irreducible
components finite, open, closed and disjoint. Their actual point spaces
therefore decompose ordinary singular cohomology by genuine restrictions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Set

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [QuasiCompact X.hom]

instance smoothFiniteTypeNoetherian : IsNoetherian X.left := by
  have : IsLocallyNoetherian Foundations.Scheme.ProjectiveSpace.complexBase := inferInstanceAs (IsLocallyNoetherian (Spec (.of ℂ)))
  have : CompactSpace Foundations.Scheme.ProjectiveSpace.complexBase := inferInstanceAs (CompactSpace (PrimeSpectrum ℂ))
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact { __ := LocallyOfFiniteType.isLocallyNoetherian X.hom }

instance finiteComponents : Finite (irreducibleComponents X.left) :=
  (finite_irreducibleComponents_of_isNoetherian (X := X.left)).to_subtype

def componentOpen (C : irreducibleComponents X.left) : X.left.Opens :=
  ⟨C.val, Foundations.Scheme.LocalDomainComponents.isOpen_irreducibleComponent_of_stalkDomains
    (Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_stalk_isDomain X.hom)
    (finite_irreducibleComponents_of_isNoetherian (X := X.left)) C.property⟩

instance componentIntegral (C : irreducibleComponents X.left) :
    IsIntegral (componentOpen X C).toScheme := by
  have : IsReduced X.left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced X.hom
  have : IrreducibleSpace (componentOpen X C).toScheme :=
    isIrreducible_iff_irreducibleSpace.mp C.property.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

def componentOver (C : irreducibleComponents X.left) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk ((componentOpen X C).ι ≫ X.hom)

def componentInclusion (C : irreducibleComponents X.left) : componentOver X C ⟶ X :=
  Over.homMk (componentOpen X C).ι rfl

instance componentInclusionOpen (C : irreducibleComponents X.left) :
    IsOpenImmersion (componentInclusion X C).left :=
  inferInstanceAs (IsOpenImmersion (componentOpen X C).ι)

instance componentInclusionClosed (C : irreducibleComponents X.left) :
    IsClosedImmersion (componentInclusion X C).left := by
  change IsClosedImmersion (componentOpen X C).ι
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact isClosed_of_mem_irreducibleComponents C.val C.property

instance componentOverIntegral (C : irreducibleComponents X.left) :
    IsIntegral (componentOver X C).left := componentIntegral X C

instance componentOverSmooth (C : irreducibleComponents X.left) :
    Smooth (componentOver X C).hom := by
  change Smooth ((componentOpen X C).ι ≫ X.hom)
  infer_instance

instance componentOverQuasiCompact (C : irreducibleComponents X.left) :
    QuasiCompact (componentOver X C).hom := by
  change QuasiCompact ((componentInclusion X C).left ≫ X.hom)
  infer_instance

instance componentOverSeparated [IsSeparated X.hom] (C : irreducibleComponents X.left) :
    IsSeparated (componentOver X C).hom := by
  change IsSeparated ((componentInclusion X C).left ≫ X.hom)
  infer_instance

theorem componentInclusion_range (C : irreducibleComponents X.left) :
    Set.range (componentInclusion X C).left = C.val := (componentOpen X C).range_ι

theorem componentInclusions_cover (x : X.left) :
    ∃ C : irreducibleComponents X.left, x ∈ Set.range (componentInclusion X C).left := by
  refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  rw [componentInclusion_range]
  exact mem_irreducibleComponent

theorem componentInclusions_disjoint :
    Pairwise (fun C D : irreducibleComponents X.left =>
      Disjoint (Set.range (componentInclusion X C).left) (Set.range (componentInclusion X D).left)) := by
  intro C D hCD
  rw [componentInclusion_range, componentInclusion_range]
  exact Foundations.Scheme.LocalDomainComponents.irreducibleComponents_disjoint_of_stalkDomains
    (Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_stalk_isDomain X.hom) C.property D.property (fun h => hCD (Subtype.ext h))

def componentPointsHomeomorph :
    (Σ C : irreducibleComponents X.left, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (componentOver X C)) ≃ₜ
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.disjointOpenFamilyPointHomeomorph X (componentOver X) (componentInclusion X)
    (componentInclusions_cover X) (componentInclusions_disjoint X)

abbrev componentPointSpaces (C : irreducibleComponents X.left) : TopCat :=
  Betti.Scheme.schemePointSpace (componentOver X C)

def componentPointSpaceIso :
    TopCat.of (Σ C, componentPointSpaces X C) ≅ Betti.Scheme.schemePointSpace X :=
  TopCat.isoOfHomeo (componentPointsHomeomorph X)

def componentBettiEquiv (n : ℕ) :
    Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n ≃ₗ[ℂ]
      (∀ C : irreducibleComponents X.left, Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) (componentOver X C) n) :=
  ((AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyFunctor (ModuleCat.of ℂ ℂ) n).mapIso
    (componentPointSpaceIso X).op).toLinearEquiv.trans
      (AlgebraicTopology.Cohomology.Singular.FiniteCoproduct.singularSigmaCohomologyEquiv (componentPointSpaces X) (ModuleCat.of ℂ ℂ) n)

theorem componentBettiEquiv_apply (n : ℕ) (a : Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n)
    (C : irreducibleComponents X.left) :
    componentBettiEquiv X n a C = Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n (componentInclusion X C) a := by
  change AlgebraicTopology.Cohomology.Singular.FiniteCoproduct.singularSigmaCohomologyEquiv (componentPointSpaces X) (ModuleCat.of ℂ ℂ) n
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ)
      (componentPointSpaceIso X).hom n a) C = _
  rw [AlgebraicTopology.Cohomology.Singular.FiniteCoproduct.singularSigmaCohomologyEquiv_apply]
  have hmap : TopCat.sigmaι (componentPointSpaces X) C ≫
      (componentPointSpaceIso X).hom =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (componentInclusion X C) := by
    ext p
    rfl
  have h := AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp (ModuleCat.of ℂ ℂ)
    (TopCat.sigmaι (componentPointSpaces X) C)
    (componentPointSpaceIso X).hom n
  rw [hmap] at h
  exact (ConcreteCategory.congr_hom h a).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Components
