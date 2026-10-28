import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularCycleFundamentalClass
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteRestrictionCoefficients

/-! # Regular Fundamental Trace -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace

noncomputable section

/-!
# Compact-relative traces of the genuine regular fundamental class

Properness makes the inverse image of the retained compact set compact.
Finite truncation there, followed by the actual ordinary relative map,
defines the trace. The proved proper naturality square identifies it with
compact restriction after genuine locally finite pushforward. The final
specialization uses the existing canonical rational regular-locus class.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
open scoped TensorProduct ChangeOfRings

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

variable (R : Type) [CommRing R] {X Y : TopCat.{0}}

/-- The actual compact-relative chain trace under a proper continuous map. -/
def properLocallyFiniteCompactRestriction (f : X ⟶ Y) (hf : IsProperMap f)
    (K : Set Y) (hK : IsCompact K) :
    LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X ⟶ RelativeScalarChains.Cycles.relativeScalarChains R Y Kᶜ :=
  LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestriction R X (f ⁻¹' K) (hf.isCompact_preimage hK) ≫
    RelativeScalarChains.Cycles.relativeScalarChainsMap R f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)

/-- This trace is precisely compact restriction of the genuine proper
locally finite pushforward. -/
theorem properLocallyFiniteCompactRestriction_eq_pushforward
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K) :
    properLocallyFiniteCompactRestriction R f hf K hK =
      LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap R f hf ≫ LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestriction R Y K hK :=
  (LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestriction_naturality R f hf K hK).symm

/-- Its value is the relative projection of the ordinary pushforward of
the actual finite truncation at the compact inverse image. -/
theorem properLocallyFiniteCompactRestriction_f
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K)
    (n : ℕ) (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n) :
    (properLocallyFiniteCompactRestriction R f hf K hK).f n c =
      (RelativeScalarChains.Cycles.relativeScalarChainProjection R Y Kᶜ).f n
        (((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f).f n
          (LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactTruncation R X (f ⁻¹' K)
            (hf.isCompact_preimage hK) n c)) := by
  rw [properLocallyFiniteCompactRestriction_eq_pushforward]
  exact LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestrictionDegree_proper_truncation R f hf K hK n c

/-- The trace of a finite chain agrees with its ordinary scalar pushforward
followed by the ordinary relative projection. -/
@[reassoc]
theorem properLocallyFiniteCompactRestriction_ordinary
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K) :
    LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap R X ≫
        properLocallyFiniteCompactRestriction R f hf K hK =
      (RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f ≫ RelativeScalarChains.Cycles.relativeScalarChainProjection R Y Kᶜ := by
  unfold properLocallyFiniteCompactRestriction
  rw [← Category.assoc, LocallyFiniteScalarRestriction.Cycles.ordinaryToLocallyFinite_comp_scalarCompactRestriction,
    RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality]

/-- The actual compact-relative trace of a locally finite homology class. -/
abbrev properLocallyFiniteCompactTrace (f : X ⟶ Y) (hf : IsProperMap f)
    (K : Set Y) (hK : IsCompact K) (n : ℕ) :
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology n ⟶ RelativeScalarChains.Cycles.relativeScalarHomology R Y Kᶜ n :=
  HomologicalComplex.homologyMap (properLocallyFiniteCompactRestriction R f hf K hK) n

/-- The trace factors through compact relative homology of the source. -/
theorem properLocallyFiniteCompactTrace_def
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K) (n : ℕ) :
    properLocallyFiniteCompactTrace R f hf K hK n =
      LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction R X (f ⁻¹' K)
          (hf.isCompact_preimage hK) n ≫
        HomologicalComplex.homologyMap
          (RelativeScalarChains.Cycles.relativeScalarChainsMap R f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n :=
  HomologicalComplex.homologyMap_comp _ _ n

/-- The homology trace is compact restriction after proper pushforward. -/
theorem properLocallyFiniteCompactTrace_eq_pushforward_restriction
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K) (n : ℕ) :
    properLocallyFiniteCompactTrace R f hf K hK n =
      LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap R f hf n ≫
        LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction R Y K hK n := by
  rw [properLocallyFiniteCompactTrace, properLocallyFiniteCompactRestriction_eq_pushforward,
    HomologicalComplex.homologyMap_comp]

/-- Finite/locally-finite trace compatibility on actual scalar homology. -/
@[reassoc]
theorem properLocallyFiniteCompactTrace_ordinary
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K) (n : ℕ) :
    HomologicalComplex.homologyMap (LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap R X) n ≫
        properLocallyFiniteCompactTrace R f hf K hK n =
      HomologicalComplex.homologyMap ((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f) n ≫
        HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainProjection R Y Kᶜ) n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun g => HomologicalComplex.homologyMap g n)
      (properLocallyFiniteCompactRestriction_ordinary R f hf K hK)

/-- Every compact trace has a finite ordinary source representative whose
pushforward is a cycle in the actual target relative quotient. -/
theorem properLocallyFiniteCompactTrace_has_finite_representative
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K) (n : ℕ)
    (u : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology n) :
    ∃ (a : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n)
      (ha : (RelativeScalarChains.Cycles.relativeScalarChainProjection R Y Kᶜ).f n
          (((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f).f n a) ∈
        AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeScalarChains.Cycles.relativeScalarChains R Y Kᶜ) n),
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (RelativeScalarChains.Cycles.relativeScalarChains R Y Kᶜ) n
        ⟨(RelativeScalarChains.Cycles.relativeScalarChainProjection R Y Kᶜ).f n
          (((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f).f n a), ha⟩ =
        properLocallyFiniteCompactTrace R f hf K hK n u := by
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) n u
  let a := LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactTruncation R X (f ⁻¹' K) (hf.isCompact_preimage hK) n c.val
  let z := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (properLocallyFiniteCompactRestriction R f hf K hK) n c
  have hz : z.val = (RelativeScalarChains.Cycles.relativeScalarChainProjection R Y Kᶜ).f n
      (((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f).f n a) :=
    properLocallyFiniteCompactRestriction_f R f hf K hK n c.val
  have ha : (RelativeScalarChains.Cycles.relativeScalarChainProjection R Y Kᶜ).f n
      (((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f).f n a) ∈
        AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeScalarChains.Cycles.relativeScalarChains R Y Kᶜ) n := by
    rw [← hz]
    exact z.property
  refine ⟨a, ha, ?_⟩
  have he : (⟨(RelativeScalarChains.Cycles.relativeScalarChainProjection R Y Kᶜ).f n
      (((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f).f n a), ha⟩ :
        AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeScalarChains.Cycles.relativeScalarChains R Y Kᶜ) n) = z := Subtype.ext hz.symm
  rw [he]
  change AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (RelativeScalarChains.Cycles.relativeScalarChains R Y Kᶜ) n
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (properLocallyFiniteCompactRestriction R f hf K hK) n c) = _
  rw [← AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, hc]

private theorem properLocallyFiniteCompactTrace_degree_transport
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K)
    {i j : ℕ} (h : i = j) (u : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology i) :
    properLocallyFiniteCompactTrace R f hf K hK j
        ((eqToHom (congrArg (fun n => (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology n) h)) u) =
      (eqToHom (congrArg (fun n => RelativeScalarChains.Cycles.relativeScalarHomology R Y Kᶜ n) h))
        (properLocallyFiniteCompactTrace R f hf K hK i u) := by
  subst j
  rfl

end Cycles

namespace DimensionCycleSupport

open OAI.AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace.Cycles

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : DimensionCycles.DimensionCycleSupport V p)

/-- The retained subset of the actual regular locus is the inverse image
under its genuine inclusion into the singular-boundary complement. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularCompactPreimage (K : Set Z.regularAmbientSpace) : Set Z.regularAnalyticSpace :=
  Z.regularComplementTopCatMap ⁻¹' K

/-- The inverse image is compact because this actual inclusion is proper. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.isCompact_regularCompactPreimage (K : Set Z.regularAmbientSpace) (hK : IsCompact K) :
    IsCompact (Z.regularCompactPreimage K) :=
  Z.isProperMap_regularComplementTopCatMap.isCompact_preimage hK

/-- The rational regular fundamental class restricts to exactly the
rationalization of the established compact integral fundamental class. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRationalLocallyFiniteFundamentalClass_restriction
    (K : Set Z.regularAnalyticSpace) (hK : IsCompact K) :
    LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction ℚ (TopCat.of Z.regularAnalyticSpace)
        K hK (2 * Z.regularComplexDimension) Z.regularRationalLocallyFiniteFundamentalClass =
      (RationalRelativeHomology.Cycles.rationalRelativeHomologyIso (TopCat.of Z.regularAnalyticSpace) Kᶜ
        (2 * Z.regularComplexDimension)).inv
        ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
          (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass Z.regularComplexDimension K hK)) := by
  change LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction ℚ (TopCat.of Z.regularAnalyticSpace)
    K hK (2 * Z.regularComplexDimension)
      (AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology
        (TopCat.of Z.regularAnalyticSpace) (2 * Z.regularComplexDimension)
        Z.regularLocallyFiniteFundamentalClass) = _
  rw [AlgebraicTopology.Duality.Poincare.LocallyFiniteRestrictionCoefficients.locallyFiniteIntegralToRationalHomology_compactRestriction,
    Z.regularLocallyFiniteFundamentalClass_restriction]

/-- In its native manifold degree, the trace is the actual relative
pushforward of the compact fundamental class with unit rational coefficient. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularNativeFundamentalCompactTrace_eq_compactFundamental
    (K : Set Z.regularAmbientSpace) (hK : IsCompact K) :
    Cycles.properLocallyFiniteCompactTrace ℚ Z.regularComplementTopCatMap
        Z.isProperMap_regularComplementTopCatMap K hK (2 * Z.regularComplexDimension)
        Z.regularRationalLocallyFiniteFundamentalClass =
      HomologicalComplex.homologyMap
        (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ Z.regularComplementTopCatMap
          (A := (Z.regularCompactPreimage K)ᶜ) (B := Kᶜ) (fun _ hx => hx))
        (2 * Z.regularComplexDimension)
        ((RationalRelativeHomology.Cycles.rationalRelativeHomologyIso (TopCat.of Z.regularAnalyticSpace)
          (Z.regularCompactPreimage K)ᶜ (2 * Z.regularComplexDimension)).inv
          ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
            (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass Z.regularComplexDimension
              (Z.regularCompactPreimage K) (Z.isCompact_regularCompactPreimage K hK)))) := by
  rw [Cycles.properLocallyFiniteCompactTrace_def]
  exact congrArg
    (HomologicalComplex.homologyMap
      (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ Z.regularComplementTopCatMap
        (A := (Z.regularCompactPreimage K)ᶜ) (B := Kᶜ) (fun _ hx => hx))
      (2 * Z.regularComplexDimension))
    (Z.regularRationalLocallyFiniteFundamentalClass_restriction
      (Z.regularCompactPreimage K) (Z.isCompact_regularCompactPreimage K hK))

/-- The actual compact-relative trace of the canonical rational regular-locus
fundamental class, in the proved codimension degree. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRationalFundamentalCompactTrace
    (K : Set Z.regularAmbientSpace) (hK : IsCompact K) :
    RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of Z.regularAmbientSpace) Kᶜ
      (2 * (V.complexDimension - p)) :=
  Cycles.properLocallyFiniteCompactTrace ℚ Z.regularComplementTopCatMap
    Z.isProperMap_regularComplementTopCatMap K hK (2 * (V.complexDimension - p))
    Z.regularRationalLocallyFiniteFundamentalClassInCodimension

/-- This is the ordinary relative pushforward of the canonical class's
restriction at the genuine compact inverse image. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRationalFundamentalCompactTrace_eq_relative_pushforward
    (K : Set Z.regularAmbientSpace) (hK : IsCompact K) :
    Z.regularRationalFundamentalCompactTrace K hK =
      HomologicalComplex.homologyMap
        (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ Z.regularComplementTopCatMap
          (A := (Z.regularCompactPreimage K)ᶜ) (B := Kᶜ) (fun _ hx => hx))
        (2 * (V.complexDimension - p))
        (LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction ℚ (TopCat.of Z.regularAnalyticSpace)
          (Z.regularCompactPreimage K) (Z.isCompact_regularCompactPreimage K hK)
          (2 * (V.complexDimension - p))
          Z.regularRationalLocallyFiniteFundamentalClassInCodimension) := by
  rw [DimensionCycles.DimensionCycleSupport.regularRationalFundamentalCompactTrace, Cycles.properLocallyFiniteCompactTrace_def]
  rfl

/-- The trace is exactly compact restriction of the already constructed
genuine rational locally finite cycle class. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRationalFundamentalCompactTrace_eq_restriction
    (K : Set Z.regularAmbientSpace) (hK : IsCompact K) :
    Z.regularRationalFundamentalCompactTrace K hK =
      LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction ℚ (TopCat.of Z.regularAmbientSpace)
        K hK (2 * (V.complexDimension - p)) Z.regularRationalCycleLocallyFiniteClass := by
  rw [DimensionCycles.DimensionCycleSupport.regularRationalFundamentalCompactTrace,
    Cycles.properLocallyFiniteCompactTrace_eq_pushforward_restriction]
  rfl

/-- Using the native regular-manifold dimension first gives the same trace
after transport through the established dimension equality. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRationalFundamentalCompactTrace_eq_transport
    (K : Set Z.regularAmbientSpace) (hK : IsCompact K) :
    Z.regularRationalFundamentalCompactTrace K hK =
      (eqToHom (congrArg
        (fun n => RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of Z.regularAmbientSpace) Kᶜ n)
        Z.regularFundamentalDegree_eq))
        (Cycles.properLocallyFiniteCompactTrace ℚ Z.regularComplementTopCatMap
          Z.isProperMap_regularComplementTopCatMap K hK (2 * Z.regularComplexDimension)
          Z.regularRationalLocallyFiniteFundamentalClass) := by
  rw [DimensionCycles.DimensionCycleSupport.regularRationalFundamentalCompactTrace,
    Z.regularRationalLocallyFiniteFundamentalClassInCodimension_eq_transport]
  exact Cycles.properLocallyFiniteCompactTrace_degree_transport ℚ Z.regularComplementTopCatMap
    Z.isProperMap_regularComplementTopCatMap K hK Z.regularFundamentalDegree_eq
    Z.regularRationalLocallyFiniteFundamentalClass

/-- The regular trace is represented by the pushforward of a genuine
finite ordinary chain on the regular locus, modulo the compact complement. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRationalFundamentalCompactTrace_has_finite_representative
    (K : Set Z.regularAmbientSpace) (hK : IsCompact K) :
    ∃ (a : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of Z.regularAnalyticSpace)).X
        (2 * (V.complexDimension - p)))
      (ha : (RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of Z.regularAmbientSpace) Kᶜ).f
          (2 * (V.complexDimension - p))
          (((RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map Z.regularComplementTopCatMap).f
            (2 * (V.complexDimension - p)) a) ∈
        AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of Z.regularAmbientSpace) Kᶜ)
          (2 * (V.complexDimension - p))),
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of Z.regularAmbientSpace) Kᶜ)
        (2 * (V.complexDimension - p))
        ⟨(RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of Z.regularAmbientSpace) Kᶜ).f
          (2 * (V.complexDimension - p))
          (((RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map Z.regularComplementTopCatMap).f
            (2 * (V.complexDimension - p)) a), ha⟩ =
        Z.regularRationalFundamentalCompactTrace K hK :=
  Cycles.properLocallyFiniteCompactTrace_has_finite_representative ℚ Z.regularComplementTopCatMap
    Z.isProperMap_regularComplementTopCatMap K hK (2 * (V.complexDimension - p))
    Z.regularRationalLocallyFiniteFundamentalClassInCodimension

end DimensionCycleSupport

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace
