import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourcePullback
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSheafCupCohomology
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourceThomIso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceRetraction

/-! # Normal Support Relative -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions

noncomputable section

section

/-! The actual supported source–Thom isomorphism intertwines relative pullback with the original two-support cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem sourceTargetIso_cup {C : Type*} [Category C] {R S A B X Y : C}
    (u : R ⟶ S) (f : S ⟶ A) (g : S ⟶ B) (eA : A ≅ X) (eAB : A ≅ B) (eB : B ≅ Y)
    (h : R ⟶ X) (cup : R ⟶ Y)
    (hp : u ≫ f ≫ eA.hom = h) (he : f ≫ eAB.hom = g) (hc : u ≫ g ≫ eB.hom = cup) :
    h ≫ (eA.symm ≪≫ eAB ≪≫ eB).hom = cup := by
  rw [← hp]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc f, he]
  exact hc

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceThomSupportedRelativeIso_cup (O U : Opens Z.regularAmbientSpace) (q : ℕ) :
    HomologicalComplex.homologyMap (SupportedSourcePullback.Constructions.relativeSourcePullbackMap
      (X := TopCat.of Z.regularAmbientSpace) (Y := TopCat.of Z.regularAnalyticSpace)
      O U (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)) q ≫
        (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha O U q).hom =
      ModuleCat.ofHom (SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace) (O : Set Z.regularAmbientSpace) U)
        (Z.regularThomComplementOpen.isOpen.preimage continuous_subtype_val)
        (O.isOpen.preimage continuous_subtype_val) 2 q
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U 2 Z.regularThomClass)) := by
  have hc := SupportSheafCupCohomology.Constructions.closedSupportGoodShiftSheafCup_cohomology (X := TopCat.of Z.regularAmbientSpace)
    Z.regularThomComplementOpen O U a (fun n hn => RegularThomSheafPurity.Constructions.regularThomSheaf_exactAt_except Z n (by omega)) q
  rw [RelativeCupShiftSections.Constructions.relativeTwoCocycleOpenRestriction_class, ha] at hc
  exact sourceTargetIso_cup
    (HomologicalComplex.homologyMap (ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections (X := TopCat.of Z.regularAmbientSpace) O U) q)
    (HomologicalComplex.homologyMap
      (((ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))) q)
    (HomologicalComplex.homologyMap
      (((ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace)
          Z.regularThomComplementOpen a)) q)
    (ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) O U q)
    (ClosedSupportThomResolution.Constructions.regularSourceThomClosedSupportIso Z a ha O U q)
    (SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z O U q) _ _
    (SupportedSourcePullback.Constructions.relativeSourcePullbackMap_cohomology (X := TopCat.of Z.regularAmbientSpace)
      (Y := TopCat.of Z.regularAnalyticSpace) O U (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) q)
    (ClosedSupportThomResolution.Constructions.regularSourceThomClosedSupportIso_cup Z a ha O U q) hc

end

section

/-! Any open complement inside a neighborhood is represented by an actual ambient open complement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (U : Opens X) (B : Opens U)

def localSupportAmbientOpen : Opens X := U.isOpenEmbedding.functor.obj B

theorem localSupportAmbientOpen_restriction :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (localSupportAmbientOpen U B : Set X) U = (B : Set U) := by
  exact congrArg (fun O : Opens U => (O : Set U)) (Opens.map_functor_eq B)

theorem localSupportAmbientOpen_union (C : Opens X) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) ((C ⊔ localSupportAmbientOpen U B : Opens X) : Set X) U =
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U ∪ (B : Set U) := by
  change AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U ∪
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (localSupportAmbientOpen U B : Set X) U = _
  rw [localSupportAmbientOpen_restriction]

variable {Y : TopCat.{0}} (f : Y ⟶ X)

theorem localSupportAmbientOpen_source :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := Y)
      (((Opens.map f).obj (localSupportAmbientOpen U B) : Opens Y) : Set Y) ((Opens.map f).obj U) =
      (SingularSheafPullback.Constructions.openPreimageMap f U) ⁻¹' (B : Set U) := by
  have he := congrArg (fun S : Set U => (SingularSheafPullback.Constructions.openPreimageMap f U) ⁻¹' S)
    (localSupportAmbientOpen_restriction U B)
  exact he

theorem localSupportAmbientOpen_mono {B D : Opens U} (h : B ≤ D) :
    localSupportAmbientOpen U B ≤ localSupportAmbientOpen U D :=
  Set.image_mono h

end

section

/-! Equality transport of relative supports preserves actual pullback and both inputs of the supported cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

theorem relativePairMap_supportEquality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A A' : Set X} {B B' : Set Y} (eA : A = A') (eB : B = B')
    (h : Set.MapsTo f A B) (h' : Set.MapsTo f A' B') (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f h n ≫
      (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) eA)).hom =
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y S n) eB)).hom ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f h' n := by
  subst A'
  subst B'
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem twoSupportCup_supportEquality (X : TopCat.{0})
    {A A' B B' : Set X} (eA : A = A') (eB : B = B')
    (hA : IsOpen A) (hA' : IsOpen A') (hB : IsOpen B) (hB' : IsOpen B') (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S (p+q))
      (congrArg₂ (fun S T : Set X => S ∪ T) eA eB))).hom
      (SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a b) =
    SupportCup.Constructions.twoSupportCohomologyCup X A' B' hA' hB' p q
      ((eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S p) eA)).hom a)
      ((eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S q) eB)).hom b) := by
  subst A'
  subst B'
  rfl

end

section

/-! The actual normal retraction splits source-relative pullback with its precise pulled-back support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {c d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)

theorem normalPairSourceRetraction_left_inverse (y : NormalPairProductSupport.Constructions.normalPairSourceOpen P hf) :
    SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf y) = y := by
  change (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm
    ((NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf y)).2) = y
  rw [NormalPairSourceSupport.Constructions.normalPairSourceInclusion_coordinates, Homeomorph.symm_apply_apply]

def normalPairRetractionComplement (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) : Set P.neighborhood :=
  (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf) ⁻¹' (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ

theorem normalPairRetractionComplement_eq_tangent (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) :
    normalPairRetractionComplement P hf K =
      (NormalPairProductSupport.Constructions.normalPairTangentMap P) ⁻¹' (SourceSupportedThomIso.Constructions.normalPairSourceTangentCompact P hf K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ := by
  ext y
  change (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm (NormalPairProductSupport.Constructions.normalPairTangentMap P y) ∉ (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) ↔
    NormalPairProductSupport.Constructions.normalPairTangentMap P y ∉ (Compacts.equiv (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
  have he := AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactHomeomorph_complement_iff (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) K
    ((NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm (NormalPairProductSupport.Constructions.normalPairTangentMap P y))
  simpa only [Homeomorph.apply_symm_apply, Set.mem_compl_iff] using he

theorem normalPairRetraction_union_complement (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) :
    P.relativeComplement ∪ normalPairRetractionComplement P hf K =
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K : Set P.neighborhood)ᶜ := by
  rw [normalPairRetractionComplement_eq_tangent]
  exact SourceSupportedThomIso.Constructions.normalPairSourceComplement_eq P hf K

theorem normalPairRetractionComplement_source (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) :
    (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) ⁻¹' normalPairRetractionComplement P hf K =
      (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ := by
  change (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf ≫ SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf) ⁻¹'
    (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ = _
  rw [NormalPairSourceRetraction.Constructions.normalPairSourceInclusion_retraction]
  rfl

theorem normalPairSourceInclusion_mapsTo_retractionComplement (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) :
    Set.MapsTo (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ
      (normalPairRetractionComplement P hf K) := by
  intro y hy
  change SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf y) ∉
    (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))
  rw [normalPairSourceRetraction_left_inverse]
  exact hy

theorem normalPairRelativeRetraction_split (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf)
        (A := normalPairRetractionComplement P hf K) (B := (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ)
        (fun _ hx => hx) q ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf)
        (normalPairSourceInclusion_mapsTo_retractionComplement P hf K) q = 𝟙 _ := by
  change HomologicalComplex.homologyMap _ q ≫ HomologicalComplex.homologyMap _ q = 𝟙 _
  rw [← HomologicalComplex.homologyMap_comp,
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id (ModuleCat.of ℚ ℚ)
      (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf)
      (normalPairSourceInclusion_mapsTo_retractionComplement P hf K) (fun _ hx => hx)
      (NormalPairSourceRetraction.Constructions.normalPairSourceInclusion_retraction P hf), HomologicalComplex.homologyMap_id]

variable [T2Space M]

def normalPairRetractionComplementOpen (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) : Opens P.neighborhood :=
  ⟨normalPairRetractionComplement P hf K,
    K.isCompact.isClosed.isOpen_compl.preimage (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf).hom.continuous⟩

end

/-! Exact compact-image complements in a normal chart and their source supports. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] [T2Space M] {c d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)

def normalPairImageComplementOpen (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) : Opens P.neighborhood :=
  ⟨(OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K : Set P.neighborhood)ᶜ, by
    rw [← normalPairRetraction_union_complement P hf K]
    exact (NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P).union
      (normalPairRetractionComplementOpen P hf K).isOpen⟩

theorem normalPairRetractionComplement_le_image (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) :
    normalPairRetractionComplementOpen P hf K ≤ normalPairImageComplementOpen P hf K := by
  change normalPairRetractionComplement P hf K ⊆
    (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K : Set P.neighborhood)ᶜ
  rw [← normalPairRetraction_union_complement P hf K]
  exact Set.subset_union_right

theorem normalPairImageComplement_source (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) :
    (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) ⁻¹' (normalPairImageComplementOpen P hf K : Set P.neighborhood) =
      (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ := by
  have hi : Function.Injective (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) :=
    Function.LeftInverse.injective (normalPairSourceRetraction_left_inverse P hf)
  change (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) ⁻¹'
    ((NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) '' (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)))ᶜ = _
  rw [Set.preimage_compl, Set.preimage_image_eq _ hi]

theorem normalPairImage_union_complement (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) :
    P.relativeComplement ∪ (normalPairImageComplementOpen P hf K : Set P.neighborhood) =
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K : Set P.neighborhood)ᶜ := by
  change P.relativeComplement ∪
    (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K : Set P.neighborhood)ᶜ = _
  apply Set.union_eq_right.mpr
  rw [← normalPairRetraction_union_complement P hf K]
  exact Set.subset_union_left

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions
