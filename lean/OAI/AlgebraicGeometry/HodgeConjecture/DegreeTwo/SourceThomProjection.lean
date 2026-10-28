import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedCupTransport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceSupportedThomIso

/-! # Source Thom Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions

noncomputable section

/-! The supported Thom projection formula on the actual compact source image. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {c d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)

def normalPairSourceRetractionMap :
    TopCat.of P.neighborhood ⟶ TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf) :=
  NormalPairProductSupport.Constructions.normalPairTangentMap P ≫ (TopCat.isoOfHomeo (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf)).inv

theorem normalPairSourceRetraction_pullback (r : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) r) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (normalPairSourceRetractionMap P hf) r b =
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairTangentMap P) r
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (TopCat.isoOfHomeo (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf)).inv r b) := by
  rw [normalPairSourceRetractionMap, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp]
  rfl

theorem normalPairSourceSupportedCohomologyIso_eq (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))
    (q : ℕ) (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ q) :
    SourceSupportedThomIso.Constructions.normalPairSourceSupportedCohomologyIso P hf K q a =
    eqToHom (congrArg
      (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) S (2*c+q))
      (SourceSupportedThomIso.Constructions.normalPairSourceComplement_eq P hf K))
      (PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso P
        (SourceSupportedThomIso.Constructions.normalPairSourceTangentCompact P hf K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ
        (SourceSupportedThomIso.Constructions.normalPairSourceTangentCompact P hf K).isCompact.isClosed.isOpen_compl q
        ((AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportHomeomorphStageCohomologyIso (ModuleCat.of ℚ ℚ)
          (X := TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentBallOpen P))
          (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) K q).inv a)) := rfl

theorem normalPairSourceSupportedCohomologyIso_projection
    (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (q r : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ q)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) r) :
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K : Set P.neighborhood)ᶜ
      (Nat.add_assoc (2*c) q r)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of P.neighborhood)
        (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K : Set P.neighborhood)ᶜ (2*c+q) r
        (SourceSupportedThomIso.Constructions.normalPairSourceSupportedCohomologyIso P hf K q a)
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (normalPairSourceRetractionMap P hf) r b)) =
    SourceSupportedThomIso.Constructions.normalPairSourceSupportedCohomologyIso P hf K (q+r)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))
        (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ q r a b) := by
  rw [normalPairSourceSupportedCohomologyIso_eq, normalPairSourceSupportedCohomologyIso_eq,
    normalPairSourceRetraction_pullback, SupportedCupTransport.Constructions.compactHomeomorphStage_inv_rightCup,
    ← SupportedCupTransport.Constructions.relativeSupportTransport_rightCup (TopCat.of P.neighborhood) (SourceSupportedThomIso.Constructions.normalPairSourceComplement_eq P hf K),
    SupportedCupTransport.Constructions.relativeDegreeCast_supportTransport (TopCat.of P.neighborhood) (SourceSupportedThomIso.Constructions.normalPairSourceComplement_eq P hf K),
    NormalPairThomProjection.Constructions.normalPairSupportedCohomologyIso_projection]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions
