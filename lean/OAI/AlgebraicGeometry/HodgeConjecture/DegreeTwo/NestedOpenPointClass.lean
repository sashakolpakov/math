import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenEmbeddingExtension
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNaturality
import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace

/-! # Nested Open Point Class -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NestedOpenPointClass.Constructions

noncomputable section

section

/-! The actual normal point dual on every open coordinate neighborhood has trace one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace

set_option backward.isDefEq.respectTransparency false

variable {d : ℕ} (U : Opens (Fin d → ℂ)) (h0 : (0 : Fin d → ℂ) ∈ U)

theorem openOrigin_mapsTo_complement :
    Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin d → ℂ)) U)
      ({⟨0,h0⟩}ᶜ : Set U) ({0}ᶜ : Set (Fin d → ℂ)) := by
  intro x hx
  change x ≠ ⟨0,h0⟩ at hx
  change (x : Fin d → ℂ) ≠ 0
  exact fun h => hx (Subtype.ext h)

def openOriginRelativeDualClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) ({⟨0,h0⟩}ᶜ : Set U) (2*d) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin d → ℂ)) U) (openOrigin_mapsTo_complement U h0)
    (2*d) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d)

def compactOpenPointDualClass :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (2*d) :=
  CompactPointNaturality.Constructions.compactPointCohomologyι (TopCat.of U) ⟨0,h0⟩ (2*d) (openOriginRelativeDualClass U h0)

theorem compactOpenPointDualClass_extension :
    AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of (Fin d → ℂ)) U (2*d)
      (compactOpenPointDualClass U h0) = CompactPointNormalization.Constructions.compactPointDualClass d := by
  have h := OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_pullback
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin d → ℂ)) U) U.isOpen.isOpenEmbedding_subtypeVal
    ⟨{⟨0,h0⟩},isCompact_singleton⟩ ⟨{0},isCompact_singleton⟩
    (by change _ '' ({⟨0,h0⟩} : Set U) = {0}; rw [Set.image_singleton]; rfl)
    (openOrigin_mapsTo_complement U h0) (2*d) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d)
  rw [OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_openSubspace] at h
  exact h

theorem compactOpenPointDualClass_trace :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := U) (compactOpenPointDualClass U h0) = 1 := by
  rw [← AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_open_apply d U, compactOpenPointDualClass_extension,
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_coordinate]
  exact CompactPointNormalization.Constructions.compactPointDualClass_normalization d

end

/-! Normal point classes extend compatibly between nested open neighborhoods. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace

set_option backward.isDefEq.respectTransparency false

abbrev opensInclusionMap {X : TopCat.{0}} {U V : Opens X} (h : U ≤ V) : TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom (ContinuousMap.inclusion h)

theorem opensInclusionMap_isOpenEmbedding {X : TopCat.{0}} {U V : Opens X} (h : U ≤ V) :
    Topology.IsOpenEmbedding (opensInclusionMap h) :=
  Topology.IsOpenEmbedding.inclusion h (U.isOpen.preimage continuous_subtype_val)

variable {d : ℕ} {U V : Opens (Fin d → ℂ)} (h : U ≤ V) (h0 : (0 : Fin d → ℂ) ∈ U)

theorem openOriginInclusion_mapsTo :
    Set.MapsTo (opensInclusionMap (X := TopCat.of (Fin d → ℂ)) h)
      ({⟨0,h0⟩}ᶜ : Set U) ({⟨0,h h0⟩}ᶜ : Set V) := by
  intro y hy hz
  exact hy (Subtype.ext (congrArg (fun z : V => z.val) (Set.mem_singleton_iff.mp hz)))

theorem openOriginRelativeDualClass_inclusion :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (opensInclusionMap (X := TopCat.of (Fin d → ℂ)) h) (openOriginInclusion_mapsTo h h0) (2*d)
      (openOriginRelativeDualClass V (h h0)) = openOriginRelativeDualClass U h0 := by
  unfold openOriginRelativeDualClass
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin d → ℂ)) V) (openOrigin_mapsTo_complement V (h h0)) (2*d) ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (opensInclusionMap (X := TopCat.of (Fin d → ℂ)) h) (openOriginInclusion_mapsTo h h0) (2*d))
      (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d) = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

theorem compactOpenPointDualClass_openInclusion :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (opensInclusionMap (X := TopCat.of (Fin d → ℂ)) h)
      (opensInclusionMap_isOpenEmbedding h) (2*d) (compactOpenPointDualClass U h0) =
      compactOpenPointDualClass V (h h0) := by
  have he := OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_pullback
    (opensInclusionMap (X := TopCat.of (Fin d → ℂ)) h) (opensInclusionMap_isOpenEmbedding h)
    ⟨{⟨0,h0⟩},isCompact_singleton⟩ ⟨{⟨0,h h0⟩},isCompact_singleton⟩
    (by
      change opensInclusionMap (X := TopCat.of (Fin d → ℂ)) h '' ({⟨0,h0⟩} : Set U) = {⟨0,h h0⟩}
      rw [Set.image_singleton]
      rfl) (openOriginInclusion_mapsTo h h0) (2*d)
    (openOriginRelativeDualClass V (h h0))
  have hc := congrArg
    (fun a => OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (opensInclusionMap (X := TopCat.of (Fin d → ℂ)) h)
      (opensInclusionMap_isOpenEmbedding h) (2*d)
      (CompactPointNaturality.Constructions.compactPointCohomologyι (TopCat.of U) ⟨0,h0⟩ (2*d) a))
    (openOriginRelativeDualClass_inclusion h h0)
  exact hc.symm.trans he

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NestedOpenPointClass.Constructions
