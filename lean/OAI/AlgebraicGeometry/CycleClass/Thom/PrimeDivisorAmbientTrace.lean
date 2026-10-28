import OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorCompactTrace
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.FundamentalDegreeTransport

/-! # Prime Divisor Ambient Trace -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorAmbientTrace

noncomputable section

section

/-! Prime-divisor integration at every actual compact ambient support
avoiding the singular boundary, in any proved equal homological degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions.Compact

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Trace.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorImmersion.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (z : {x : X.left // Order.coheight x = 1})

local instance : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Scheme.RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z))) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (Scheme.RegularSupport.Constructions.regularToAmbient X (SchemeDivisor.Purity.Constructions.primeSupport X z))).t2Space

local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X (OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z)
local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "n" => OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorCompactTrace.Constructions.divisorDegree X z

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem isCompact_regularPreimage (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hL : (L : Set T) ⊆ G) :
    IsCompact (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹' (L : Set T)) := by
  let K : Compacts G := (AlgebraicTopology.Duality.Poincare.CompactOpenIndex.openCompactsOrderIso G).symm ⟨L, hL⟩
  exact (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).isProperMap_regularComplementTopCatMap.isCompact_preimage K.isCompact

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem regularCompactProjection_eq (K : Compacts G) :
    PrimeDivisorCompactTrace.Constructions.regularCompactProjection X z K =
    HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z)
        (A := (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹' (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T))ᶜ)
        (B := (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ) (fun _ hx => hx)) n
      (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplexDimension
        (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹' (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T))
        (isCompact_regularPreimage X z (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K) (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_subset (X := T) G K))) := by
  have he : (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplementTopCatMap ⁻¹' (K : Set G) =
      PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹' (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T) := by
    ext x
    constructor
    · intro hx
      exact ⟨(PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplementTopCatMap x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      change (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplementTopCatMap x ∈ (K : Set G)
      exact (Subtype.ext he) ▸ hy
  exact ProperImage.Projection.Constructions.Construction.rationalCompactFundamentalClass_map_support_congr
    (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplexDimension
    (M := (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularAnalyticSpace) (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z) he
    ((PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).isProperMap_regularComplementTopCatMap.isCompact_preimage K.isCompact)
    (isCompact_regularPreimage X z (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K) (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_subset (X := T) G K))
    (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ (PrimeDivisorCompactTrace.Constructions.regularCompactPairMapsTo X z K) (fun _ hx => hx)

/-- The integration formula uses the literal compact preimage under the
actual regular inclusion into the full smooth ambient scheme. -/
theorem absoluteDivisorClass_compactTrace
    (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hL : (L : Set T) ⊆ G)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (L : Set T)ᶜ n) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) 2 n (PrimeDivisorTrace.Constructions.primeDivisor_trace_degree X z)
      (SchemeDivisor.Trace.Constructions.Class.absoluteDivisorClass X z) (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) T L n b) =
    Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (L : Set T)ᶜ n b
      (HomologicalComplex.homologyMap
        (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z)
          (A := (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹' (L : Set T))ᶜ) (B := (L : Set T)ᶜ) (fun _ hx => hx)) n
        (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplexDimension
          (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹' (L : Set T)) (isCompact_regularPreimage X z L hL))) := by
  let K : Compacts G := (AlgebraicTopology.Duality.Poincare.CompactOpenIndex.openCompactsOrderIso G).symm ⟨L, hL⟩
  let L' := AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K
  have himage : L' = L := congrArg Subtype.val ((AlgebraicTopology.Duality.Poincare.CompactOpenIndex.openCompactsOrderIso G).apply_symm_apply ⟨L, hL⟩)
  let P : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) → Prop := fun C =>
    ∀ (hC : (C : Set T) ⊆ G) (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (C : Set T)ᶜ n),
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) 2 n (PrimeDivisorTrace.Constructions.primeDivisor_trace_degree X z)
      (SchemeDivisor.Trace.Constructions.Class.absoluteDivisorClass X z) (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) T C n a) =
    Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (C : Set T)ᶜ n a
      (HomologicalComplex.homologyMap
        (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z)
          (A := (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹' (C : Set T))ᶜ) (B := (C : Set T)ᶜ) (fun _ hx => hx)) n
        (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplexDimension
          (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹' (C : Set T)) (isCompact_regularPreimage X z C hC)))
  have hP : P L' := by
    intro hC a
    exact (PrimeDivisorCompactTrace.Constructions.absoluteDivisorClass_compactTrace_openSupport X z K a).trans
      (congrArg (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (L' : Set T)ᶜ n a)
        (regularCompactProjection_eq X z K))
  exact (Eq.mp (congrArg P himage) hP) hL b

/-- The same trace with a common degree for summing different prime divisors. -/
theorem absoluteDivisorClass_compactTrace_inDegree
    (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hL : (L : Set T) ⊆ G)
    (k : ℕ) (hk : PrimeDivisorCompactTrace.Constructions.divisorDegree X z = k)
    (hdeg : 2 + k = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (L : Set T)ᶜ k) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) 2 k hdeg (SchemeDivisor.Trace.Constructions.Class.absoluteDivisorClass X z)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) T L k b) =
    Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (L : Set T)ᶜ k b
      (HomologicalComplex.homologyMap
        (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z)
          (A := (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹' (L : Set T))ᶜ) (B := (L : Set T)ᶜ) (fun _ hx => hx)) k
        (ProperImage.FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplexDimension
          (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹' (L : Set T)) (isCompact_regularPreimage X z L hL) k hk)) := by
  cases hk
  exact absoluteDivisorClass_compactTrace X z L hL b

end Constructions.Compact

end

/-! A smooth open containing the retained divisor support computes the
same actual divisor integral, with its own native complex charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.Compact

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Trace.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorImmersion.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (z : {x : X.left // Order.coheight x = 1})

local instance : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Scheme.RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z))) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (Scheme.RegularSupport.Constructions.regularToAmbient X (SchemeDivisor.Purity.Constructions.primeSupport X z))).t2Space

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X (OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z)

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem isCompact_openRegularPreimage
    {P : TopCat.{0}} (j : P ⟶ (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularAnalyticSpace)
    (hj : Topology.IsOpenEmbedding j)
    (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hL : (L : Set T) ⊆ G)
    (hRange : PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹' (L : Set T) ⊆ Set.range j) :
    IsCompact ((j ≫ PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z) ⁻¹' (L : Set T)) :=
  hj.isEmbedding.isInducing.isCompact_preimage' (isCompact_regularPreimage X z L hL) hRange

/-- Actual compact integration may be computed on any retained smooth
support open, preserving the canonical complex orientation. -/
theorem absoluteDivisorClass_compactTrace_from_open
    (d : ℕ) {P : Type} [TopologicalSpace P] [T2Space P]
    [ChartedSpace (Fin d → ℂ) P] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 P]
    (j : TopCat.of P ⟶ (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularAnalyticSpace)
    (hj : Topology.IsOpenEmbedding j)
    (hl : IsLocalDiffeomorph 𝓘(ℂ, Fin d → ℂ)
      𝓘(ℂ, (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularAnalyticModel) ω j)
    (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hL : (L : Set T) ⊆ G)
    (hRange : PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹' (L : Set T) ⊆ Set.range j)
    (n : ℕ) (hd : 2 * d = n) (hz : PrimeDivisorCompactTrace.Constructions.divisorDegree X z = n)
    (hdeg : 2 + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (L : Set T)ᶜ n) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) 2 n hdeg (SchemeDivisor.Trace.Constructions.Class.absoluteDivisorClass X z)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) T L n b) =
    Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (L : Set T)ᶜ n b
      (HomologicalComplex.homologyMap
        (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (j ≫ PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z)
          (A := ((j ≫ PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z) ⁻¹' (L : Set T))ᶜ)
          (B := (L : Set T)ᶜ) (fun _ hx => hx)) n
        (ProperImage.FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree d
          ((j ≫ PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z) ⁻¹' (L : Set T))
          (isCompact_openRegularPreimage X z j hj L hL hRange) n hd)) := by
  let K := PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z ⁻¹' (L : Set T)
  let J := j ⁻¹' K
  have hK : IsCompact K := isCompact_regularPreimage X z L hL
  have hJ : IsCompact J := isCompact_openRegularPreimage X z j hj L hL hRange
  have hJK : j '' J = K := Set.image_preimage_eq_of_subset hRange
  have hclass := ProperImage.FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree_injective_toSupport
    d (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplexDimension
    (M := P) (N := (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularAnalyticSpace) j hj.injective hl J hJ K hK hJK
    (fun _ hx => hx) n hd hz
  have hc := ConcreteCategory.congr_hom
    (Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ j (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z)
      (A := Jᶜ) (B := Kᶜ) (C := (L : Set T)ᶜ) (fun _ hx => hx) (fun _ hx => hx) n)
    (ProperImage.FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree d J hJ n hd)
  have hproj := absoluteDivisorClass_compactTrace_inDegree X z L hL n hz hdeg b
  exact hproj.trans (congrArg (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (L : Set T)ᶜ n b)
    ((congrArg (HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (PrimeDivisorCompactTrace.Constructions.regularAmbientMap X z)
        (A := Kᶜ) (B := (L : Set T)ᶜ) (fun _ hx => hx)) n) hclass.symm).trans hc))

end Constructions.Compact

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorAmbientTrace
