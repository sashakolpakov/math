import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceSupportedThomIso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactHomeomorphInverseStage
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairCompactGysin
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularLocalGysinTrace

/-! # Source Compact Gysin -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceCompactGysin.Constructions

noncomputable section

/-! The all-degree local source Gysin map and its exact supported-stage meaning. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {c d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)

def normalPairSourceCompactGysin (q : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) q →ₗ[ℚ]
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) (2*c+q) :=
  (NormalPairCompactGysin.Constructions.normalPairCompactGysin P q).comp
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      (X := TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentBallOpen P))
      (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) q).inv.hom

theorem normalPairSourceCompactGysin_stage_supported (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))
      (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ q) :
    normalPairSourceCompactGysin P hf q
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) K q a) =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K) (2*c+q)
      (SourceSupportedThomIso.Constructions.normalPairSourceSupportedCohomologyIso P hf K q a) := by
  let L := SourceSupportedThomIso.Constructions.normalPairSourceTangentCompact P hf K
  let e := AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportHomeomorphStageCohomologyIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentBallOpen P))
    (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) K q
  have hi := ConcreteCategory.congr_hom (CompactHomeomorphInverseStage.Constructions.compactHomeomorph_inverse_stage
    (X := TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentBallOpen P))
    (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) K q) a
  have hs := NormalPairCompactGysin.Constructions.normalPairCompactGysin_stage_supported P L q (e.inv a)
  have hc := CompactPointNaturality.Constructions.compactSupportCohomologyι_supportCast (TopCat.of P.neighborhood)
    (NormalPairCompactSupport.Constructions.normalPairCompactSupport P L) (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K)
    (NormalPairSourceSupport.Constructions.normalPairSourceCompactSupport_image P hf K)
    (NormalPairProductSupport.Constructions.normalPairCombinedComplement P (L : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ)
    (NormalPairCompactSupport.Constructions.normalPairCompactSupport_complement P L) (SourceSupportedThomIso.Constructions.normalPairSourceComplement_eq P hf K) (2*c+q)
    (PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso P (L : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ
      L.isCompact.isClosed.isOpen_compl q (e.inv a))
  exact (congrArg (NormalPairCompactGysin.Constructions.normalPairCompactGysin P q) hi).trans (hs.trans hc)

theorem normalPairSourceCompactGysin_top
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (2*d)) :
    eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
      (Nat.mul_add 2 c d).symm) (normalPairSourceCompactGysin P hf (2*d) a) =
    RegularLocalGysinTrace.Constructions.normalPairSourceCompactGysinTop P hf a := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceCompactGysin.Constructions
