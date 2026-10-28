import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceRetraction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceCompactGysin
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCupAssociativity

/-! # Source Gysin Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceGysinProjection.Constructions

noncomputable section

/-! The actual local source Gysin map satisfies the compact-support projection formula. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {c d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)

theorem normalPairSourceCompactGysin_projection (q r : ℕ)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) q)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) r) :
    eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
      (Nat.add_assoc (2*c) q r))
      (CompactCohomologyCup.Constructions.compactCohomologyRightCup (TopCat.of P.neighborhood) (2*c+q) r b
        (SourceCompactGysin.Constructions.normalPairSourceCompactGysin P hf q a)) =
    SourceCompactGysin.Constructions.normalPairSourceCompactGysin P hf (q+r)
      (CompactCohomologyCup.Constructions.compactCohomologyRightCup (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) q r
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) r b) a) := by
  obtain ⟨K,a,rfl⟩ := AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ)
    (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) q a
  rw [SourceCompactGysin.Constructions.normalPairSourceCompactGysin_stage_supported, CompactCohomologyCup.Constructions.compactCohomologyRightCup_stage,
    CompactCohomologyCup.Constructions.compactCohomologyRightCup_stage, SourceCompactGysin.Constructions.normalPairSourceCompactGysin_stage_supported,
    CompactCupAssociativity.Constructions.compactCohomologyι_degreeCast (TopCat.of P.neighborhood)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K) (Nat.add_assoc (2*c) q r)]
  apply congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
    (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K) (2*c+(q+r)))
  rw [← RelativeCupAssociativity.Constructions.relativeCohomologyCast_eqToHom (TopCat.of P.neighborhood)
    (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K : Set P.neighborhood)ᶜ
    (Nat.add_assoc (2*c) q r)]
  exact NormalPairSourceRetraction.Constructions.normalPairSourceSupportedCohomologyIso_ambient_projection P hf K q r a b

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceGysinProjection.Constructions
