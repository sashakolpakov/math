import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.RestrictionDegree
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.DimensionDrop
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicEtale
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential

/-! # Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open.Constructions.Construction

noncomputable section

section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- The image support in its prescribed codimension when dimension is preserved. -/
def imageCycleSupport {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Reduction.Constructions.imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) : Geometric.DimensionCycles.DimensionCycleSupport Y q :=
  ⟨Reduction.Constructions.imageSupport f Z, Reduction.Constructions.imageCodimension_eq f p q hdeg Z hdim⟩

/-- The actual proper support map, retaining the complex structure morphisms. -/
def supportImageOverMap {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Reduction.Constructions.imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    Z.toOver ⟶ (imageCycleSupport f p q hdeg Z hdim).toOver :=
  Over.homMk (SupportMap.Constructions.Construction.supportImageMap f hf Z) (SupportMap.Constructions.Construction.supportImageMap_over f hf Z)

/-- A dimension-preserving proper support map has an actual finite etale
generic open whose source and target are both smooth. -/
theorem supportImageOverMap_exists_good_open {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Reduction.Constructions.imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    let T := imageCycleSupport f p q hdeg Z hdim
    let i := supportImageOverMap f hf p q hdeg Z hdim
    ∃ U : T.scheme.Opens, genericPoint T.scheme ∈ U ∧
      IsFinite (i.left ∣_ U) ∧ Etale (i.left ∣_ U) ∧
      Smooth (U.ι ≫ T.structureMap) ∧
      Smooth ((i.left ⁻¹ᵁ U).ι ≫ Z.structureMap) := by
  let T := imageCycleSupport f p q hdeg Z hdim
  let i := supportImageOverMap f hf p q hdeg Z hdim
  let : IsIntegral Z.toOver.left := inferInstanceAs (IsIntegral Z.scheme)
  let : IsIntegral T.toOver.left := inferInstanceAs (IsIntegral T.scheme)
  let : IsProper i.left := SupportMap.Constructions.Construction.supportImageMap_isProper f hf Z
  let : IsProper T.structureMap := T.projectivePresentation.isProper
  let : IsNoetherian T.toOver.left := Foundations.Scheme.ClosedProjective.isNoetherian_of_isProper_toSpec T.structureMap
  have hi : i.left ≫ T.structureMap = Z.structureMap := SupportMap.Constructions.Construction.supportImageMap_over f hf Z
  obtain ⟨U, hU, hfin, het, hsT, hsZ⟩ := SmoothEtaleOpen.Constructions.Construction.exists_generic_smooth_finiteEtale_open
    i.left T.structureMap (SupportMap.Constructions.Construction.supportImageMap_genericPoint f hf Z) (by
      rw [hi]
      exact hdim)
  refine ⟨U, hU, hfin, het, hsT, ?_⟩
  rwa [hi] at hsZ

/-- The omitted part of a support is a genuine algebraic closed subset
of the ambient variety. -/
def supportOpenBoundary {Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {q : ℕ}
    (T : Geometric.DimensionCycles.DimensionCycleSupport Y q) (U : T.scheme.Opens) : Closeds Y.carrier :=
  ⟨T.inclusion '' (U : Set T.scheme)ᶜ,
    T.inclusion.isClosedMap _ U.isOpen.isClosed_compl⟩

theorem supportOpenBoundary_subset {Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {q : ℕ}
    (T : Geometric.DimensionCycles.DimensionCycleSupport Y q) (U : T.scheme.Opens) :
    (supportOpenBoundary T U : Set Y.carrier) ⊆ T.1 := by
  rintro x ⟨z, _, rfl⟩
  rw [← Geometric.GenericPoint.range_reducedSupportι T.1]
  exact Set.mem_range_self z

theorem genericPoint_not_mem_supportOpenBoundary {Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {q : ℕ}
    (T : Geometric.DimensionCycles.DimensionCycleSupport Y q) (U : T.scheme.Opens) (hU : genericPoint T.scheme ∈ U) :
    T.genericPoint ∉ supportOpenBoundary T U := by
  rintro ⟨z, hz, he⟩
  have he' : z = genericPoint T.scheme :=
    T.inclusion.isClosedEmbedding.injective (he.trans T.inclusion_genericPoint.symm)
  exact hz (he'.symm ▸ hU)

/-- Removing a dense open from a support leaves only subsets of strictly
higher codimension than the cycle itself. -/
theorem supportOpenBoundary_codimension {Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {q : ℕ}
    (T : Geometric.DimensionCycles.DimensionCycleSupport Y q) (U : T.scheme.Opens) (hU : genericPoint T.scheme ∈ U)
    (A : IrreducibleCloseds Y.carrier) (hA : (A : Set Y.carrier) ⊆ supportOpenBoundary T U) :
    q < Geometric.DimensionCycles.dimensionCodimension Y A := by
  have hle : A ≤ T.1 := hA.trans (supportOpenBoundary_subset T U)
  have hne : A ≠ T.1 := by
    intro he
    subst A
    have hη : T.genericPoint ∈ (T.1 : Set Y.carrier) := by
      rw [← T.genericPoint_spec]
      exact subset_closure (Set.mem_singleton T.genericPoint)
    exact genericPoint_not_mem_supportOpenBoundary T U hU (hA hη)
  have hd := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt A T.1 Y.structureMap (lt_of_le_of_ne hle hne)
  have ha := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension Y A
  have ht := T.dimension_add_codimension
  omega

end

section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential
open scoped _root_.Manifold ContDiff

local instance supportOver_isIntegral {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) : IsIntegral Z.toOver.left :=
  inferInstanceAs (IsIntegral Z.scheme)

/-- Native open immersions of smooth complex schemes are analytic local diffeomorphisms. -/
theorem isLocalDiffeomorph_nativeScheme_openImmersion
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [IsIntegral Y.left]
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y) [IsOpenImmersion f.left] :
    IsLocalDiffeomorph
      (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
      (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ))
      ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  intro x
  exact AnalyticLocalInverseAt.Constructions.ProperImage.Construction.isLocalDiffeomorphAt_of_bijective_mfderiv _ (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map f ω) x
    (ComplexPoints.Analytic.IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective f x)

/-- A smooth support open maps into the canonical regular locus. -/
def smoothSupportOpenToRegular {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus) :
    AnalyticRestriction.Constructions.Construction.openSchemeOver Z.toOver U ⟶ Z.regularOver :=
  Over.homMk (Z.scheme.homOfLE hU) (by
    change Z.scheme.homOfLE hU ≫ (Z.structureMap.smoothLocus.ι ≫ Z.structureMap) = U.ι ≫ Z.structureMap
    rw [← Category.assoc, Scheme.homOfLE_ι])

instance smoothSupportOpenToRegular_isOpenImmersion {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus) :
    IsOpenImmersion (smoothSupportOpenToRegular Z U hU).left :=
  inferInstanceAs (IsOpenImmersion (Z.scheme.homOfLE hU))

theorem smoothSupportOpenToRegular_inclusion {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus) :
    smoothSupportOpenToRegular Z U hU ≫ Z.regularToSupport = AnalyticRestriction.Constructions.Construction.openSchemeInclusion Z.toOver U := by
  apply Over.OverMorphism.ext
  exact Z.scheme.homOfLE_ι hU

/-- Every nonempty open of a support has the regular locus's native
complex dimension, as measured by its actual function field. -/
theorem supportOpen_complexDimension {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) [Nonempty U] :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AnalyticRestriction.Constructions.Construction.openSchemeOver Z.toOver U).hom =
      Z.regularComplexDimension := by
  let : IsIntegral Z.toOver.left := inferInstanceAs (IsIntegral Z.scheme)
  let : IsIntegral (AnalyticRestriction.Constructions.Construction.openSchemeOver Z.toOver U).left := inferInstanceAs (IsIntegral U.toScheme)
  let : LocallyOfFiniteType (AnalyticRestriction.Constructions.Construction.openSchemeOver Z.toOver U).hom :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ Z.structureMap))
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension]
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (U.ι ≫ Z.structureMap) = _
  rw [Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_open]
  exact Z.regularComplexDimension_eq_supportDimension.symm

/-- The image in the regular locus is exactly the points above the
chosen algebraic open of the support. -/
theorem smoothSupportOpenToRegular_range {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus) :
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (smoothSupportOpenToRegular Z U hU)) =
      Z.regularAnalyticInclusion ⁻¹' (AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen Z.toOver U : Set Z.analyticSpace) := by
  have hcomp (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AnalyticRestriction.Constructions.Construction.openSchemeOver Z.toOver U)) :
      Z.regularAnalyticInclusion (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (smoothSupportOpenToRegular Z U hU) x) =
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AnalyticRestriction.Constructions.Construction.openSchemeInclusion Z.toOver U) x := by
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map Z.regularToSupport
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (smoothSupportOpenToRegular Z U hU) x) = _
    rw [← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, smoothSupportOpenToRegular_inclusion]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change Z.regularAnalyticInclusion (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (smoothSupportOpenToRegular Z U hU) z) ∈
      (AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen Z.toOver U : Set Z.analyticSpace)
    rw [hcomp]
    exact (AnalyticRestriction.Constructions.Construction.openSchemePointHomeomorph Z.toOver U z).property
  · intro hx
    let z := (AnalyticRestriction.Constructions.Construction.openSchemePointHomeomorph Z.toOver U).symm ⟨Z.regularAnalyticInclusion x, hx⟩
    refine ⟨z, Z.isOpenEmbedding_regularAnalyticInclusion.injective ?_⟩
    rw [hcomp]
    exact congrArg Subtype.val ((AnalyticRestriction.Constructions.Construction.openSchemePointHomeomorph Z.toOver U).apply_symm_apply
      ⟨Z.regularAnalyticInclusion x, hx⟩)

end

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- Membership in the omitted support boundary is exactly failure of
membership in the chosen open before applying the closed inclusion. -/
theorem supportOpenBoundary_preimage {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) :
    Z.inclusion ⁻¹' (supportOpenBoundary Z U : Set V.carrier) = (U : Set Z.scheme)ᶜ := by
  exact Set.preimage_image_eq _ Z.inclusion.isClosedEmbedding.injective

/-- A support's singular boundary lies in the complement of every
smooth open of the support. -/
theorem singularBoundary_subset_supportOpenBoundary {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus) :
    Geometric.StratumDimension.supportSingularBoundary Z.1 V.structureMap ⊆ (supportOpenBoundary Z U : Set V.carrier) := by
  rintro x ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  intro hzU
  exact hz (hU hzU)

/-- The ambient complement of the omitted support boundary is contained
in the canonical regular ambient open. -/
theorem boundaryComplement_subset_regularAmbient {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus) :
    (CompactProjection.Constructions.Construction.algebraicComplementOpen V (supportOpenBoundary Z U) : Set V.analyticSpace) ⊆
      Z.regularAmbientOpen := by
  intro x hx hs
  exact hx (singularBoundary_subset_supportOpenBoundary Z U hU hs)

/-- A smooth inverse image of the chosen target open contains all source
support points whose ambient image avoids the target's omitted boundary. -/
theorem sourceSingularBoundary_maps_into_supportOpenBoundary
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p) (T : Geometric.DimensionCycles.DimensionCycleSupport Y q)
    (f : X.toOver ⟶ Y.toOver) (i : Z.scheme ⟶ T.scheme)
    (hi : i ≫ T.inclusion = Z.inclusion ≫ SupportMap.Constructions.Construction.algebraicMap f)
    (U : T.scheme.Opens) (hU : i ⁻¹ᵁ U ≤ Z.structureMap.smoothLocus) :
    Geometric.StratumDimension.supportSingularBoundary Z.1 X.structureMap ⊆
      SupportMap.Constructions.Construction.algebraicMap f ⁻¹' (supportOpenBoundary T U : Set Y.carrier) := by
  rintro x ⟨z, hz, rfl⟩
  refine ⟨i z, ?_, ?_⟩
  · intro hzU
    exact hz (hU hzU)
  · exact congrArg (fun k : Z.scheme ⟶ Y.carrier => k z) hi

/-- On native complex points, the same algebraic containment ensures
that compact preimages avoid the source singular boundary. -/
theorem boundaryComplement_preimage_subset_regularAmbient
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p) (T : Geometric.DimensionCycles.DimensionCycleSupport Y q)
    (f : X.toOver ⟶ Y.toOver) (i : Z.scheme ⟶ T.scheme)
    (hi : i ≫ T.inclusion = Z.inclusion ≫ SupportMap.Constructions.Construction.algebraicMap f)
    (U : T.scheme.Opens) (hU : i ⁻¹ᵁ U ≤ Z.structureMap.smoothLocus) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹'
        (CompactProjection.Constructions.Construction.algebraicComplementOpen Y (supportOpenBoundary T U) : Set Y.analyticSpace) ⊆
      Z.regularAmbientOpen := by
  intro x hx hs
  have hb := sourceSingularBoundary_maps_into_supportOpenBoundary Z T f i hi U hU hs
  exact hx hb

/-- An analytic support point whose ambient image avoids the omitted
boundary belongs to the chosen support open. -/
theorem supportPoint_mem_open_of_boundaryComplement
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (x : Z.analyticSpace)
    (hx : Z.analyticInclusion x ∈ CompactProjection.Constructions.Construction.algebraicComplementOpen V (supportOpenBoundary Z U)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ U := by
  by_contra hn
  exact hx ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x, hn, rfl⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open.Constructions.Construction
