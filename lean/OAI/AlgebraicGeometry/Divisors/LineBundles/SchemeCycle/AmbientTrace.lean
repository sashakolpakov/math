import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CompactTrace
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.FundamentalDegreeTransport

/-! # Ambient Trace -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.AmbientTrace.BundleCycles

noncomputable section

section

/-! Canonical cycle integration at every actual compact ambient support
avoiding the singular boundary, in any proved equal homological degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (Z : IrreducibleCloseds X.left) (p : ℕ)
  (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

local instance : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z)).t2Space

local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z
local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "n" => OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CompactTrace.BundleCycles.schemeCycleTraceDegree X Z

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem schemeCycle_isCompact_regularPreimage (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hL : (L : Set T) ⊆ G) :
    IsCompact (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp ⁻¹' (L : Set T)) := by
  let K : Compacts G := (AlgebraicTopology.Duality.Poincare.CompactOpenIndex.openCompactsOrderIso G).symm ⟨L, hL⟩
  exact (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).isProperMap_regularComplementTopCatMap.isCompact_preimage K.isCompact

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem schemeCycleRegularCompactProjection_eq (K : Compacts G) :
    CompactTrace.BundleCycles.schemeCycleRegularCompactProjection X Z p hp K =
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp)
        (A := (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp ⁻¹' (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T))ᶜ)
        (B := (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ) (fun _ hx => hx)) n
      (CycleClass.Thom.ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularComplexDimension
        (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp ⁻¹' (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T))
        (schemeCycle_isCompact_regularPreimage X Z p hp (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K) (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_subset (X := T) G K))) := by
  have he : (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularComplementTopCatMap ⁻¹' (K : Set G) =
      CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp ⁻¹' (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T) := by
    ext x
    constructor
    · intro hx
      exact ⟨(Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularComplementTopCatMap x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      change (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularComplementTopCatMap x ∈ (K : Set G)
      exact (Subtype.ext he) ▸ hy
  exact CycleClass.Thom.ProperImage.Projection.Constructions.Construction.rationalCompactFundamentalClass_map_support_congr
    (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularComplexDimension
    (M := (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularAnalyticSpace) (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp) he
    ((Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).isProperMap_regularComplementTopCatMap.isCompact_preimage K.isCompact)
    (schemeCycle_isCompact_regularPreimage X Z p hp (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K) (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_subset (X := T) G K))
    (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ (CompactTrace.BundleCycles.schemeCycleRegularCompactPairMapsTo X Z p hp K) (fun _ hx => hx)

/-- The integration formula uses the literal compact preimage under the
actual regular inclusion into the full smooth ambient scheme. -/
theorem schemeCycleClass_compactTrace
    (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hL : (L : Set T) ⊆ G)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (L : Set T)ᶜ n) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (2 * p) n (FundamentalTrace.BundleCycles.schemeCycle_trace_degree X Z p hp)
      (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X Z p hp) (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) T L n b) =
    CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (L : Set T)ᶜ n b
      (HomologicalComplex.homologyMap
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp)
          (A := (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp ⁻¹' (L : Set T))ᶜ) (B := (L : Set T)ᶜ) (fun _ hx => hx)) n
        (CycleClass.Thom.ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularComplexDimension
          (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp ⁻¹' (L : Set T)) (schemeCycle_isCompact_regularPreimage X Z p hp L hL))) := by
  let K : Compacts G := (AlgebraicTopology.Duality.Poincare.CompactOpenIndex.openCompactsOrderIso G).symm ⟨L, hL⟩
  let L' := AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K
  have himage : L' = L := congrArg Subtype.val ((AlgebraicTopology.Duality.Poincare.CompactOpenIndex.openCompactsOrderIso G).apply_symm_apply ⟨L, hL⟩)
  let P : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) → Prop := fun C =>
    ∀ (hC : (C : Set T) ⊆ G) (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (C : Set T)ᶜ n),
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (2 * p) n (FundamentalTrace.BundleCycles.schemeCycle_trace_degree X Z p hp)
      (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X Z p hp) (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) T C n a) =
    CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (C : Set T)ᶜ n a
      (HomologicalComplex.homologyMap
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp)
          (A := (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp ⁻¹' (C : Set T))ᶜ) (B := (C : Set T)ᶜ) (fun _ hx => hx)) n
        (CycleClass.Thom.ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularComplexDimension
          (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp ⁻¹' (C : Set T)) (schemeCycle_isCompact_regularPreimage X Z p hp C hC)))
  have hP : P L' := by
    intro hC a
    exact (CompactTrace.BundleCycles.schemeCycleClass_compactTrace_openSupport X Z p hp K a).trans
      (congrArg (CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (L' : Set T)ᶜ n a)
        (schemeCycleRegularCompactProjection_eq X Z p hp K))
  exact (Eq.mp (congrArg P himage) hP) hL b

/-- The same trace with a common degree for summing different cycle supports. -/
theorem schemeCycleClass_compactTrace_inDegree
    (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hL : (L : Set T) ⊆ G)
    (k : ℕ) (hk : CompactTrace.BundleCycles.schemeCycleTraceDegree X Z = k)
    (hdeg : 2 * p + k = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (L : Set T)ᶜ k) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (2 * p) k hdeg (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X Z p hp)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) T L k b) =
    CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (L : Set T)ᶜ k b
      (HomologicalComplex.homologyMap
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp)
          (A := (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp ⁻¹' (L : Set T))ᶜ) (B := (L : Set T)ᶜ) (fun _ hx => hx)) k
        (CycleClass.Thom.ProperImage.FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularComplexDimension
          (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp ⁻¹' (L : Set T)) (schemeCycle_isCompact_regularPreimage X Z p hp L hL) k hk)) := by
  cases hk
  exact schemeCycleClass_compactTrace X Z p hp L hL b

end

/-! A smooth open containing the retained cycle support computes the
same actual cycle integral, with its own native complex charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (Z : IrreducibleCloseds X.left) (p : ℕ)
  (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

local instance : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z)).t2Space

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem schemeCycle_isCompact_openRegularPreimage
    {P : TopCat.{0}} (j : P ⟶ (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularAnalyticSpace)
    (hj : Topology.IsOpenEmbedding j)
    (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hL : (L : Set T) ⊆ G)
    (hRange : CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp ⁻¹' (L : Set T) ⊆ Set.range j) :
    IsCompact ((j ≫ CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp) ⁻¹' (L : Set T)) :=
  hj.isEmbedding.isInducing.isCompact_preimage' (schemeCycle_isCompact_regularPreimage X Z p hp L hL) hRange

/-- Actual compact integration may be computed on any retained smooth
support open, preserving the canonical complex orientation. -/
theorem schemeCycleClass_compactTrace_from_open
    (d : ℕ) {P : Type} [TopologicalSpace P] [T2Space P]
    [ChartedSpace (Fin d → ℂ) P] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 P]
    (j : TopCat.of P ⟶ (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularAnalyticSpace)
    (hj : Topology.IsOpenEmbedding j)
    (hl : IsLocalDiffeomorph 𝓘(ℂ, Fin d → ℂ)
      𝓘(ℂ, (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularAnalyticModel) ω j)
    (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hL : (L : Set T) ⊆ G)
    (hRange : CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp ⁻¹' (L : Set T) ⊆ Set.range j)
    (n : ℕ) (hd : 2 * d = n) (hz : CompactTrace.BundleCycles.schemeCycleTraceDegree X Z = n)
    (hdeg : 2 * p + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (L : Set T)ᶜ n) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (2 * p) n hdeg (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X Z p hp)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) T L n b) =
    CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (L : Set T)ᶜ n b
      (HomologicalComplex.homologyMap
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (j ≫ CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp)
          (A := ((j ≫ CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp) ⁻¹' (L : Set T))ᶜ)
          (B := (L : Set T)ᶜ) (fun _ hx => hx)) n
        (CycleClass.Thom.ProperImage.FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree d
          ((j ≫ CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp) ⁻¹' (L : Set T))
          (schemeCycle_isCompact_openRegularPreimage X Z p hp j hj L hL hRange) n hd)) := by
  let K := CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp ⁻¹' (L : Set T)
  let J := j ⁻¹' K
  have hK : IsCompact K := schemeCycle_isCompact_regularPreimage X Z p hp L hL
  have hJ : IsCompact J := schemeCycle_isCompact_openRegularPreimage X Z p hp j hj L hL hRange
  have hJK : j '' J = K := Set.image_preimage_eq_of_subset hRange
  have hclass := CycleClass.Thom.ProperImage.FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree_injective_toSupport
    d (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularComplexDimension
    (M := P) (N := (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularAnalyticSpace) j hj.injective hl J hJ K hK hJK
    (fun _ hx => hx) n hd hz
  have hc := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ j (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp)
      (A := Jᶜ) (B := Kᶜ) (C := (L : Set T)ᶜ) (fun _ hx => hx) (fun _ hx => hx) n)
    (CycleClass.Thom.ProperImage.FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree d J hJ n hd)
  have hproj := schemeCycleClass_compactTrace_inDegree X Z p hp L hL n hz hdeg b
  exact hproj.trans (congrArg (CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (L : Set T)ᶜ n b)
    ((congrArg (HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (CompactTrace.BundleCycles.schemeCycleRegularAmbientMap X Z p hp)
        (A := Kᶜ) (B := (L : Set T)ᶜ) (fun _ hx => hx)) n) hclass.symm).trans hc))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.AmbientTrace.BundleCycles
