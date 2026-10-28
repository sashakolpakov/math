import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Support
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.SupportFields
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Reduction

/-! # Dimension Drop -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.DimensionDrop.Constructions.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- Every closed irreducible subset of a dimension-dropping image has
codimension strictly greater than the prescribed target cycle degree. -/
theorem dimensionDrop_image_codimension
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Reduction.Constructions.imageSupport f Z) Y.structureMap ≠
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap)
    (T : IrreducibleCloseds Y.carrier) (hT : (T : Set Y.carrier) ⊆ Reduction.Constructions.imageSupport f Z) :
    q < Geometric.DimensionCycles.dimensionCodimension Y T := by
  have hd := SupportFields.Constructions.Construction.imageSupport_dimension_lt_of_ne f hf Z hdim
  have hle := (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono Y.structureMap).monotone hT
  have hs := Z.dimension_add_codimension
  have ht := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension Y T
  rw [← X.complexDimension_eq_transcendenceDimension] at hs
  rw [← Y.complexDimension_eq_transcendenceDimension] at ht
  omega

/-- In a dimension drop, the genuine geometric fundamental cycle
pushes to zero in ordinary rational homology. -/
theorem geometricCycleFundamentalClass_push_eq_zero_of_dimension_drop
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Reduction.Constructions.imageSupport f Z) Y.structureMap ≠
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    HomologicalComplex.homologyMap
      ((Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f))
        (2 * Z.regularComplexDimension) Z.geometricCycleFundamentalClass = 0 := by
  let F : TopCat.of X.analyticSpace ⟶ TopCat.of Y.analyticSpace := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f
  let W : Closeds Y.carrier := ⟨(Reduction.Constructions.imageSupport f Z : Set Y.carrier), (Reduction.Constructions.imageSupport f Z).isClosed⟩
  have hn : (q + q) + 2 * Z.regularComplexDimension = 2 * Y.complexDimension := by
    have hs := Z.regularGeometricTrace_degree
    omega
  apply CompactProjection.Constructions.Construction.ordinaryHomology_eq_of_compactProjections_outside_closed Y W q
    (2 * Z.regularComplexDimension) hn
    (dimensionDrop_image_codimension f hf p q hdeg Z hdim) _ 0
  intro L hL
  let K : Compacts X.analyticSpace :=
    ⟨F ⁻¹' (L : Set Y.analyticSpace), (L.isCompact.isClosed.preimage F.hom.continuous).isCompact⟩
  have hK : ∀ x ∈ (K : Set X.analyticSpace), x ∉ Set.range Z.analyticInclusion := by
    intro x hx hz
    have hz' : X.analyticUnderlying x ∈ (Z.1 : Set X.carrier) := by
      rwa [Z.range_analyticInclusion] at hz
    have hy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (F x) ∈ (Reduction.Constructions.imageSupport f Z : Set Y.carrier) := by
      rw [Reduction.Constructions.imageSupport_eq_image f hf Z]
      exact ⟨X.analyticUnderlying x, hz', (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying_map f x).symm⟩
    exact hL hx hy
  have hz := Support.Constructions.Construction.geometricCycleFundamentalClass_projection_eq_zero Z K hK
  have hc := ConcreteCategory.congr_hom
    (CompactProjection.Constructions.Construction.homologyPushforward_compactProjection F (L : Set Y.analyticSpace)
      (2 * Z.regularComplexDimension)) Z.geometricCycleFundamentalClass
  change HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of Y.analyticSpace) (L : Set Y.analyticSpace)ᶜ)
      (2 * Z.regularComplexDimension)
      (HomologicalComplex.homologyMap ((Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map F)
        (2 * Z.regularComplexDimension) Z.geometricCycleFundamentalClass) =
    HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ F (A := (F ⁻¹' (L : Set Y.analyticSpace))ᶜ)
        (B := (L : Set Y.analyticSpace)ᶜ) (fun _ hx => hx))
      (2 * Z.regularComplexDimension)
      (HomologicalComplex.homologyMap
        (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of X.analyticSpace) (K : Set X.analyticSpace)ᶜ)
        (2 * Z.regularComplexDimension) Z.geometricCycleFundamentalClass) at hc
  rw [hz, map_zero] at hc
  exact hc.trans (map_zero _).symm

/-- The preceding vanishing in any equal homology degree, written
using the actual Poincare cap map. -/
theorem poincareClass_push_eq_zero_of_dimension_drop
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Reduction.Constructions.imageSupport f Z) Y.structureMap ≠
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap)
    (n : ℕ) (hn : 2 * Z.regularComplexDimension = n)
    (hpn : (p + p) + n = 2 * X.complexDimension) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) n
      ((X.poincareDuality (p + p) n hpn).hom Z.geometricCycleClass) = 0 := by
  subst n
  exact geometricCycleFundamentalClass_push_eq_zero_of_dimension_drop f hf p q hdeg Z hdim

/-- Proper pushforward commutes with the geometric cycle class on
every irreducible generator whose image has smaller dimension. -/
theorem compatibility_generator_of_dimension_drop
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Reduction.Constructions.imageSupport f Z) Y.structureMap ≠
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    Y.geometricCycleClassMap q (Reduction.Constructions.cyclePushforwardGenerator f p q hdeg Z) =
      Reduction.Constructions.cohomologyPushforward f hf p q hdeg Z.geometricCycleClass := by
  have hp : p ≤ X.complexDimension := by
    rw [X.complexDimension_eq_transcendenceDimension]
    exact Z.codimension_le_ambient
  rw [Reduction.Constructions.cyclePushforwardGenerator, dite_eq_right hdim, map_zero]
  apply (Reduction.Constructions.Construction.eq_pushforward_iff_poincare f hf p q hdeg hp 0 Z.geometricCycleClass).mpr
  exact (Y.poincareDuality (q + q) (2 * (X.complexDimension - p))
    (Reduction.Constructions.targetComplementDegree p q hdeg hp)).hom.hom.map_zero.trans
    (poincareClass_push_eq_zero_of_dimension_drop f hf p q hdeg Z hdim
    (2 * (X.complexDimension - p)) Z.regularFundamentalDegree_eq
    (Reduction.Constructions.sourceComplementDegree X p hp)).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.DimensionDrop.Constructions.Construction
