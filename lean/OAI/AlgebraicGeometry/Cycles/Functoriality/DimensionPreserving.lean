import OAI.AlgebraicGeometry.Cycles.Functoriality.CompactCompatibility
import OAI.AlgebraicGeometry.Cycles.Functoriality.Support

/-! # Dimension Preserving -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.DimensionPreserving.Construction

noncomputable section

section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

/-- The actual Poincare cap of a dimension-preserving irreducible cycle
pushes forward with its generic residue degree as multiplicity. -/
theorem poincareClass_push_degree_of_dimension_eq
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (UnitCap.imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap)
    (n : ℕ) (hp : (p + p) + n = 2 * X.complexDimension)
    (hq : (q + q) + n = 2 * Y.complexDimension) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) n
      ((X.poincareDuality (p + p) n hp).hom Z.geometricCycleClass) =
    (f.left.residueDegree Z.genericPoint : ℚ) •
      (Y.poincareDuality (q + q) n hq).hom
        (ImageOpen.Construction.imageCycleSupport f p q hdeg Z hdim).geometricCycleClass := by
  let T := ImageOpen.Construction.imageCycleSupport f p q hdeg Z hdim
  let i := ImageOpen.Construction.supportImageOverMap f hf p q hdeg Z hdim
  let : IsIntegral Z.toOver.left := inferInstanceAs (IsIntegral Z.scheme)
  let : IsIntegral T.toOver.left := inferInstanceAs (IsIntegral T.scheme)
  have hη : i.left (genericPoint Z.toOver.left) = genericPoint T.toOver.left :=
    SupportMap.Construction.supportImageMap_genericPoint f hf Z
  have hi : i ≫ T.toAmbient = Z.toAmbient ≫ f :=
    Support.Construction.supportImageOverMap_inclusion f hf p q hdeg Z hdim
  obtain ⟨U, hU, hfin, het, hsT, hsZ⟩ :=
    ImageOpen.Construction.supportImageOverMap_exists_good_open f hf p q hdeg Z hdim
  let : Nonempty U := ⟨⟨genericPoint T.scheme, hU⟩⟩
  let A := i.left ⁻¹ᵁ U
  let : Nonempty A := ⟨⟨genericPoint Z.scheme, by
    change i.left (genericPoint Z.scheme) ∈ U
    exact hη.symm ▸ hU⟩⟩
  let S₀ := AnalyticRestriction.Construction.openSchemeOver Z.toOver A
  let T₀ := AnalyticRestriction.Construction.openSchemeOver T.toOver U
  let : Smooth (A.ι ≫ Z.structureMap) := hsZ
  let : Smooth (U.ι ≫ T.structureMap) := hsT
  let : Smooth S₀.hom := hsZ
  let : Smooth T₀.hom := hsT
  have hAZ : A ≤ Z.structureMap.smoothLocus := RestrictionDegree.Construction.open_subset_smoothLocus Z.structureMap A
  have hUT : U ≤ T.structureMap.smoothLocus := RestrictionDegree.Construction.open_subset_smoothLocus T.structureMap U
  let jZ := ImageOpen.Construction.smoothSupportOpenToRegular Z A hAZ
  let jT := ImageOpen.Construction.smoothSupportOpenToRegular T U hUT
  let h := AnalyticRestriction.Construction.restrictedSchemeMap i U
  let : IsFinite h.left := hfin
  let : Etale h.left := het
  let : IsIntegral Z.regularOver.left := inferInstanceAs (IsIntegral Z.regularScheme)
  let : IsIntegral T.regularOver.left := inferInstanceAs (IsIntegral T.regularScheme)
  let : Smooth Z.regularOver.hom := inferInstanceAs (Smooth Z.regularToBase)
  let : Smooth T.regularOver.hom := inferInstanceAs (Smooth T.regularToBase)
  have hip : IsProperMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map i).isProperMap
  have hproper := AnalyticRestriction.Construction.restrictedSchemeMap_isProperMap i hip U
  let d := Betti.AffineDimension.Realization.functionFieldDifferentialDimension S₀.hom
  let e := Betti.AffineDimension.Realization.functionFieldDifferentialDimension T₀.hom
  have hdZ : d = Z.regularComplexDimension := ImageOpen.Construction.supportOpen_complexDimension Z A
  have heT : e = T.regularComplexDimension := ImageOpen.Construction.supportOpen_complexDimension T U
  have hZn : 2 * Z.regularComplexDimension = n := by
    have hd := Z.regularGeometricTrace_degree
    omega
  have hTn : 2 * T.regularComplexDimension = n := by
    have hd := T.regularGeometricTrace_degree
    omega
  have hdn : 2 * d = n := (congrArg (fun k : ℕ => 2 * k) hdZ).trans hZn
  have hen : 2 * e = n := (congrArg (fun k : ℕ => 2 * k) heT).trans hTn
  have hcard : ∀ y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T₀,
      Nat.card (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map h ⁻¹' {y}) = f.left.residueDegree Z.genericPoint := by
    intro y
    exact (RestrictionDegree.Construction.restrictedSchemeMap_fiber_card i hη U y).trans (ResidueDegree.Construction.supportImageMap_residueDegree f hf Z)
  let B := ImageOpen.Construction.supportOpenBoundary T U
  apply CompactProjection.Construction.ordinaryHomology_eq_of_compactProjections_outside_closed Y B q n hq
    (ImageOpen.Construction.supportOpenBoundary_codimension T U hU) _ _
  intro L hL
  have hiLeft : i.left ≫ T.inclusion = Z.inclusion ≫ SupportMap.Construction.algebraicMap f :=
    SupportMap.Construction.supportImageMap_inclusion f hf Z
  have hLZ := (BoundaryContainment.Construction.boundaryComplement_preimage_subset_regularAmbient Z T f i.left hiLeft U hAZ).trans'
    (Set.preimage_mono hL)
  have hLT := hL.trans (BoundaryContainment.Construction.boundaryComplement_subset_regularAmbient T U hUT)
  have hRangeZ := Support.Construction.sourceRegularPreimage_subset_smoothSupportOpen_range Z T f i hi U hAZ
    (L : Set Y.analyticSpace) hL
  have hRangeT := Support.Construction.regularPreimage_subset_smoothSupportOpen_range T U hUT
    (L : Set Y.analyticSpace) hL
  have hcompat := CompactCompatibility.Construction.poincareCycleClass_compact_covering_compatibility Z T f d e
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map jZ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map jT)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion jZ)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion jT)
    (ImageOpen.Construction.isLocalDiffeomorph_nativeScheme_openImmersion jZ)
    (ImageOpen.Construction.isLocalDiffeomorph_nativeScheme_openImmersion jT)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map h) hproper
    (IntrinsicEtale.Construction.isLocalDiffeomorph_nativeScheme_affineEtale h)
    (Support.Construction.restricted_support_cover_square Z T f i hi U hUT hAZ)
    (f.left.residueDegree Z.genericPoint) hcard n hdn hen hZn hTn hp hq L hLZ hLT hRangeZ hRangeT
  exact hcompat.trans ((HomologicalComplex.homologyMap
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of Y.analyticSpace) (L : Set Y.analyticSpace)ᶜ) n).hom.map_smul
      (f.left.residueDegree Z.genericPoint : ℚ)
      ((Y.poincareDuality (q + q) n hq).hom T.geometricCycleClass)).symm

end

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Proper pushforward commutes with geometric classes on each
dimension-preserving irreducible generator. -/
theorem compatibility_generator_of_dimension_eq
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (UnitCap.imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    Y.geometricCycleClassMap q (UnitCap.cyclePushforwardGenerator f p q hdeg Z) =
      UnitCap.cohomologyPushforward f hf p q hdeg Z.geometricCycleClass := by
  have hp : p ≤ X.complexDimension := by
    rw [X.complexDimension_eq_transcendenceDimension]
    exact Z.codimension_le_ambient
  rw [Reduction.Construction.image_class_of_dimension_eq f p q hdeg Z hdim]
  apply (Reduction.Construction.eq_pushforward_iff_poincare f hf p q hdeg hp _ Z.geometricCycleClass).mpr
  exact (Y.poincareDuality (q + q) (2 * (X.complexDimension - p))
    (UnitCap.targetComplementDegree p q hdeg hp)).hom.hom.map_smul
      (f.left.residueDegree Z.genericPoint : ℚ)
      (ImageOpen.Construction.imageCycleSupport f p q hdeg Z hdim).geometricCycleClass |>.trans
    (poincareClass_push_degree_of_dimension_eq f hf p q hdeg Z hdim
      (2 * (X.complexDimension - p)) (UnitCap.sourceComplementDegree X p hp)
      (UnitCap.targetComplementDegree p q hdeg hp)).symm

/-- Proper pushforward of rational algebraic cycles commutes with the
geometric cycle class, with the stated dimension degree shift. -/
theorem cycleClass_proper_pushforward
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X p) :
    Y.geometricCycleClassMap q (UnitCap.cyclePushforward f hf p q hdeg z) =
      UnitCap.cohomologyPushforward f hf p q hdeg (X.geometricCycleClassMap p z) := by
  apply (Reduction.Construction.compatibility_iff_generators f hf p q hdeg).mpr _ z
  intro Z
  by_cases hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (UnitCap.imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap
  · exact compatibility_generator_of_dimension_eq f hf p q hdeg Z hdim
  · exact DimensionDrop.Construction.compatibility_generator_of_dimension_drop f hf p q hdeg Z hdim

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.DimensionPreserving.Construction
