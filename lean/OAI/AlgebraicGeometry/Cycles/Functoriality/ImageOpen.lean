import OAI.AlgebraicGeometry.Cycles.Functoriality.RestrictionDegree
import OAI.AlgebraicGeometry.Cycles.Functoriality.DimensionDrop
import OAI.AlgebraicGeometry.Cycles.Functoriality.IntrinsicEtale
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential

/-! # Image Open -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.ImageOpen.Construction

noncomputable section

section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- The image support in its prescribed codimension when dimension is preserved. -/
def imageCycleSupport {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (UnitCap.imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport Y q :=
  ⟨UnitCap.imageSupport f Z, UnitCap.imageCodimension_eq f p q hdeg Z hdim⟩

/-- The actual proper support map, retaining the complex structure morphisms. -/
def supportImageOverMap {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (UnitCap.imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    Z.toOver ⟶ (imageCycleSupport f p q hdeg Z hdim).toOver :=
  Over.homMk (SupportMap.Construction.supportImageMap f hf Z) (SupportMap.Construction.supportImageMap_over f hf Z)

/-- A dimension-preserving proper support map has an actual finite etale
generic open whose source and target are both smooth. -/
theorem supportImageOverMap_exists_good_open {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (UnitCap.imageSupport f Z) Y.structureMap =
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
  let : IsProper i.left := SupportMap.Construction.supportImageMap_isProper f hf Z
  let : IsProper T.structureMap := T.projectivePresentation.isProper
  let : IsNoetherian T.toOver.left := Foundations.Scheme.ClosedProjective.isNoetherian_of_isProper_toSpec T.structureMap
  have hi : i.left ≫ T.structureMap = Z.structureMap := SupportMap.Construction.supportImageMap_over f hf Z
  obtain ⟨U, hU, hfin, het, hsT, hsZ⟩ := GenericEtale.Construction.exists_generic_smooth_finiteEtale_open
    i.left T.structureMap (SupportMap.Construction.supportImageMap_genericPoint f hf Z) (by
      rw [hi]
      exact hdim)
  refine ⟨U, hU, hfin, het, hsT, ?_⟩
  rwa [hi] at hsZ

/-- The omitted part of a support is a genuine algebraic closed subset
of the ambient variety. -/
def supportOpenBoundary {Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {q : ℕ}
    (T : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport Y q) (U : T.scheme.Opens) : Closeds Y.carrier :=
  ⟨T.inclusion '' (U : Set T.scheme)ᶜ,
    T.inclusion.isClosedMap _ U.isOpen.isClosed_compl⟩

theorem supportOpenBoundary_subset {Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {q : ℕ}
    (T : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport Y q) (U : T.scheme.Opens) :
    (supportOpenBoundary T U : Set Y.carrier) ⊆ T.1 := by
  rintro x ⟨z, _, rfl⟩
  rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι T.1]
  exact Set.mem_range_self z

theorem genericPoint_not_mem_supportOpenBoundary {Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {q : ℕ}
    (T : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport Y q) (U : T.scheme.Opens) (hU : genericPoint T.scheme ∈ U) :
    T.genericPoint ∉ supportOpenBoundary T U := by
  rintro ⟨z, hz, he⟩
  have he' : z = genericPoint T.scheme :=
    T.inclusion.isClosedEmbedding.injective (he.trans T.inclusion_genericPoint.symm)
  exact hz (he'.symm ▸ hU)

/-- Removing a dense open from a support leaves only subsets of strictly
higher codimension than the cycle itself. -/
theorem supportOpenBoundary_codimension {Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {q : ℕ}
    (T : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport Y q) (U : T.scheme.Opens) (hU : genericPoint T.scheme ∈ U)
    (A : IrreducibleCloseds Y.carrier) (hA : (A : Set Y.carrier) ⊆ supportOpenBoundary T U) :
    q < CycleClass.Geometric.DimensionCycles.dimensionCodimension Y A := by
  have hle : A ≤ T.1 := hA.trans (supportOpenBoundary_subset T U)
  have hne : A ≠ T.1 := by
    intro he
    subst A
    have hη : T.genericPoint ∈ (T.1 : Set Y.carrier) := by
      rw [← T.genericPoint_spec]
      exact subset_closure (Set.mem_singleton T.genericPoint)
    exact genericPoint_not_mem_supportOpenBoundary T U hU (hA hη)
  have hd := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt A T.1 Y.structureMap (lt_of_le_of_ne hle hne)
  have ha := CycleClass.Geometric.DimensionCycles.supportDimension_add_dimensionCodimension Y A
  have ht := T.dimension_add_codimension
  omega

end

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential
open scoped _root_.Manifold ContDiff

local instance supportOver_isIntegral {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : IsIntegral Z.toOver.left :=
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
  exact AnalyticInverse.Construction.isLocalDiffeomorphAt_of_bijective_mfderiv _ (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map f ω) x
    (ComplexPoints.Analytic.IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective f x)

/-- A smooth support open maps into the canonical regular locus. -/
def smoothSupportOpenToRegular {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus) :
    AnalyticRestriction.Construction.openSchemeOver Z.toOver U ⟶ Z.regularOver :=
  Over.homMk (Z.scheme.homOfLE hU) (by
    change Z.scheme.homOfLE hU ≫ (Z.structureMap.smoothLocus.ι ≫ Z.structureMap) = U.ι ≫ Z.structureMap
    rw [← Category.assoc, Scheme.homOfLE_ι])

instance smoothSupportOpenToRegular_isOpenImmersion {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus) :
    IsOpenImmersion (smoothSupportOpenToRegular Z U hU).left :=
  inferInstanceAs (IsOpenImmersion (Z.scheme.homOfLE hU))

theorem smoothSupportOpenToRegular_inclusion {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus) :
    smoothSupportOpenToRegular Z U hU ≫ Z.regularToSupport = AnalyticRestriction.Construction.openSchemeInclusion Z.toOver U := by
  apply Over.OverMorphism.ext
  exact Z.scheme.homOfLE_ι hU

/-- Every nonempty open of a support has the regular locus's native
complex dimension, as measured by its actual function field. -/
theorem supportOpen_complexDimension {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) [Nonempty U] :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AnalyticRestriction.Construction.openSchemeOver Z.toOver U).hom =
      Z.regularComplexDimension := by
  let : IsIntegral Z.toOver.left := inferInstanceAs (IsIntegral Z.scheme)
  let : IsIntegral (AnalyticRestriction.Construction.openSchemeOver Z.toOver U).left := inferInstanceAs (IsIntegral U.toScheme)
  let : LocallyOfFiniteType (AnalyticRestriction.Construction.openSchemeOver Z.toOver U).hom :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ Z.structureMap))
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension]
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (U.ι ≫ Z.structureMap) = _
  rw [Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_open]
  exact Z.regularComplexDimension_eq_supportDimension.symm

/-- The image in the regular locus is exactly the points above the
chosen algebraic open of the support. -/
theorem smoothSupportOpenToRegular_range {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus) :
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (smoothSupportOpenToRegular Z U hU)) =
      Z.regularAnalyticInclusion ⁻¹' (AnalyticRestriction.Construction.schemeAnalyticOpen Z.toOver U : Set Z.analyticSpace) := by
  have hcomp (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AnalyticRestriction.Construction.openSchemeOver Z.toOver U)) :
      Z.regularAnalyticInclusion (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (smoothSupportOpenToRegular Z U hU) x) =
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AnalyticRestriction.Construction.openSchemeInclusion Z.toOver U) x := by
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map Z.regularToSupport
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (smoothSupportOpenToRegular Z U hU) x) = _
    rw [← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, smoothSupportOpenToRegular_inclusion]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change Z.regularAnalyticInclusion (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (smoothSupportOpenToRegular Z U hU) z) ∈
      (AnalyticRestriction.Construction.schemeAnalyticOpen Z.toOver U : Set Z.analyticSpace)
    rw [hcomp]
    exact (AnalyticRestriction.Construction.openSchemePointHomeomorph Z.toOver U z).property
  · intro hx
    let z := (AnalyticRestriction.Construction.openSchemePointHomeomorph Z.toOver U).symm ⟨Z.regularAnalyticInclusion x, hx⟩
    refine ⟨z, Z.isOpenEmbedding_regularAnalyticInclusion.injective ?_⟩
    rw [hcomp]
    exact congrArg Subtype.val ((AnalyticRestriction.Construction.openSchemePointHomeomorph Z.toOver U).apply_symm_apply
      ⟨Z.regularAnalyticInclusion x, hx⟩)

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.ImageOpen.Construction
