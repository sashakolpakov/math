import OAI.AlgebraicGeometry.CycleClass.Thom.Open.HolomorphicEmbeddingRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.LocalGraph
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic

/-! # Affine Coordinates -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates.Constructions

/-! The genuine normalization divisor cover lifts holomorphically into the chosen affine normalization source on every retained fiber. Its polynomial coordinates inherit the original common compact bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Regular OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W

local notation "ML" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale.sourceOpen V W z))) → ℂ

theorem cover_ambient_square : Analytic.Constructions.sourceAmbientMap V W z ≫ Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W =
    Open.Constructions.Etale.coverMap V W z ≫ Analytic.Constructions.targetAmbientMap V W z := by
  simpa only [Analytic.Constructions.sourceAmbientMap, Open.Constructions.Regular.targetToRegular_ambient, Analytic.Constructions.targetAmbientMap] using Open.Constructions.Regular.regularCover_ambient_square V W z

theorem cover_liftBase_eq : Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.liftBase (Analytic.Constructions.sourceAmbientMap V W z) (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) =
    EtaleGraphOpenImmersion.Constructions.etaleBase (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) := by
  funext x
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (Analytic.Constructions.sourceAmbientMap V W z) (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) x).symm.trans
    ((congrArg (fun f => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x) (cover_ambient_square V W z)).trans
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) x))

variable (U : Opens V.analyticSpace)

abbrev coverSource := GraphOpenImmersion.Constructions.graphSourceOpen (EtaleGraphOpenImmersion.Constructions.etaleBase (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z))
  (EtaleGraphOpenImmersion.Constructions.etaleBase_analytic (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z)) U

def coverToLiftSource : coverSource V W z U → Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.liftSource (Analytic.Constructions.sourceAmbientMap V W z) (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) U :=
  fun x => ⟨x.val, (congrArg (fun t : V.analyticSpace => t ∈ U)
    (congrFun (cover_liftBase_eq V W z) x.val)).mpr x.property⟩

theorem coverToLiftSource_analytic : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, ML) ω (coverToLiftSource V W z U) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.liftSource (Analytic.Constructions.sourceAmbientMap V W z) (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) U)
    (coverToLiftSource V W z U) ω).mp
  exact (show ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, ML) ω
    (Subtype.val : coverSource V W z U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Open.Constructions.Etale.sourceOpen V W z)) from contMDiff_subtype_val)

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (U : Set V.analyticSpace) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

local notation "MX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

def coverAffineLift : coverSource V W z U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X :=
  Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.sourceLift a (Analytic.Constructions.sourceAmbientMap V W z) (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) U hcover ∘ coverToLiftSource V W z U

theorem coverAffineLift_analytic : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, MX) ω (coverAffineLift V W z U a hcover) :=
  (Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.sourceLift_analytic a (Analytic.Constructions.sourceAmbientMap V W z) (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) U hcover).comp
    (coverToLiftSource_analytic V W z U)

theorem coverAffineLift_commutes (x : coverSource V W z U) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a (coverAffineLift V W z U a hcover x) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Analytic.Constructions.sourceAmbientMap V W z) x.val :=
  Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.sourceLift_commutes a (Analytic.Constructions.sourceAmbientMap V W z) (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) U hcover (coverToLiftSource V W z U x)

variable [IsAffine X.left] {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

def coverAffineCoordinates : coverSource V W z U → Fin d → ℂ :=
  Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f ∘ coverAffineLift V W z U a hcover

theorem coverAffineCoordinates_analytic :
    ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, Fin d → ℂ) ω (coverAffineCoordinates V W z U a hcover f) :=
  (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f).comp (coverAffineLift_analytic V W z U a hcover)

theorem coverAffineCoordinates_bound (K : Set (Fin d → ℂ))
    (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U →
      Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K) (x : coverSource V W z U) :
    coverAffineCoordinates V W z U a hcover f x ∈ K :=
  Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.sourceLift_bound a (Analytic.Constructions.sourceAmbientMap V W z) (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) U hcover
    (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) K hb (coverToLiftSource V W z U x)

end AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates.Constructions.GraphEmbedding

/-! The actual lifted polynomial coordinates embed the retained normalization divisor cover; hence its literal local graph is a topological embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1}) (U : Opens V.analyticSpace)
  {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (U : Set V.analyticSpace) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

theorem coverAffineLift_isEmbedding : Topology.IsEmbedding (coverAffineLift V W z U a hcover) := by
  apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion a).isEmbedding.of_comp_iff.mp
  have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a ∘ coverAffineLift V W z U a hcover =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Analytic.Constructions.sourceAmbientMap V W z) ∘
        (Subtype.val : coverSource V W z U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Open.Constructions.Etale.sourceOpen V W z)) := by
    funext x
    exact coverAffineLift_commutes V W z U a hcover x
  rw [he]
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (Analytic.Constructions.sourceAmbientMap V W z)).comp .subtypeVal

variable [IsAffine X.left] {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

theorem coverAffineCoordinates_isEmbedding (hf : Function.Surjective f) :
    Topology.IsEmbedding (coverAffineCoordinates V W z U a hcover f) :=
  (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_closedEmbedding f hf).isEmbedding.comp (coverAffineLift_isEmbedding V W z U a hcover)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance (priority := low) : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)

theorem coverAffineGraph_isEmbedding (hf : Function.Surjective f) :
    Topology.IsEmbedding (EtaleLocalGraph.Constructions.localGraph (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U
      (coverAffineCoordinates V W z U a hcover f)) :=
  Topology.IsEmbedding.of_comp
    (EtaleLocalGraph.Constructions.localGraph_analytic (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U
      (coverAffineCoordinates V W z U a hcover f) (coverAffineCoordinates_analytic V W z U a hcover f)).continuous
    (continuous_snd : Continuous (Prod.snd : U × (Fin d → ℂ) → (Fin d → ℂ)))
    (coverAffineCoordinates_isEmbedding V W z U a hcover f hf)

end AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates.Constructions.GraphEmbedding

end

end OAI
