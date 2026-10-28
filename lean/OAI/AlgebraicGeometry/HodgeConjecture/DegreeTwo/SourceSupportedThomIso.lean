import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairSupportedCupIso

/-! # Source Supported Thom Iso -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceSupportedThomIso.Constructions

noncomputable section

/-! All-degree local Thom isomorphism with an arbitrary actual compact source support. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {c d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)

abbrev normalPairSourceTangentCompact (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) :
    Compacts (NormalPairProductSupport.Constructions.normalPairTangentSpace P) := Compacts.equiv (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) K

theorem normalPairSourceComplement_eq (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) :
    NormalPairProductSupport.Constructions.normalPairCombinedComplement P (normalPairSourceTangentCompact P hf K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ =
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K : Set P.neighborhood)ᶜ :=
  (NormalPairCompactSupport.Constructions.normalPairCompactSupport_complement P (normalPairSourceTangentCompact P hf K)).trans
    (congrArg (fun L : Compacts P.neighborhood => (L : Set P.neighborhood)ᶜ)
      (NormalPairSourceSupport.Constructions.normalPairSourceCompactSupport_image P hf K))

def normalPairSourceSupportedCohomologyIso (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))
      (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ q ≃ₗ[ℚ]
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K : Set P.neighborhood)ᶜ (2*c+q) := by
  let e := AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportHomeomorphStageCohomologyIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentBallOpen P))
    (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) K q
  let t := PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso P
    (normalPairSourceTangentCompact P hf K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ
    (normalPairSourceTangentCompact P hf K).isCompact.isClosed.isOpen_compl q
  let s := eqToIso (congrArg
    (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) A (2*c+q))
    (normalPairSourceComplement_eq P hf K))
  exact (e.symm.toLinearEquiv.trans t).trans s.toLinearEquiv

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceSupportedThomIso.Constructions
