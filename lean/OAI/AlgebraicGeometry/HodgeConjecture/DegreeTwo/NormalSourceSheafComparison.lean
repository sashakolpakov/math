import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalStalkQuasiIso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafPullback
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceRetraction

/-! # Normal Source Sheaf Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSourceSheafComparison.Constructions

noncomputable section

/-! The native source pullback is a stalk quasi-isomorphism along a normal pair. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

section NormalPair

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {c d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)

def normalPairSourceOrdinaryCohomologyIso (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) n ≅
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) n where
  hom := AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) n
  inv := AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf) n
  hom_inv_id := by
    rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp,
      AlgebraicTopology.Cohomology.Singular.Homotopy.singularCohomologyPullback_eq (ModuleCat.of ℚ ℚ) (NormalPairSourceRetraction.Constructions.normalPairSourceRetractionHomotopy P hf),
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id]
  inv_hom_id := by
    rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp, NormalPairSourceRetraction.Constructions.normalPairSourceInclusion_retraction,
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id]

theorem normalPairSourcePullback_quasiIso :
    QuasiIso (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf)) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso ((normalPairSourceOrdinaryCohomologyIso P hf n).hom)
  infer_instance

end NormalPair

variable {X Y : TopCat.{0}} [MetrizableSpace Y] {f : Y ⟶ X} {y : Y} {c d : ℕ}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f y) (hf : Topology.IsEmbedding f)

include P hf

theorem normalPairSourceOpenSheafPullback_quasiIso :
    QuasiIso (SingularSheafPullback.Constructions.singularOpenPreimageSheafMap (ModuleCat.of ℚ ℚ) f P.openNeighborhood) := by
  have := AlgebraicTopology.Cohomology.Singular.OpenParacompact.paracompactSpace_open_of_metrizable Y ((Opens.map f).obj P.openNeighborhood)
  have := AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.quasiIso_singularCochainsToOpenSheafSections_of_paracompact ℚ Y
    ((Opens.map f).obj P.openNeighborhood)
  have : QuasiIso (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (SingularSheafPullback.Constructions.openPreimageMap f P.openNeighborhood)) :=
    normalPairSourcePullback_quasiIso P hf
  unfold SingularSheafPullback.Constructions.singularOpenPreimageSheafMap
  infer_instance

theorem normalPairSourceSheafPullback_stalk_quasiIso :
    QuasiIso (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainMap (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) f) (f y)) := by
  apply LocalStalkQuasiIso.Constructions.sheafComplexLift_stalk_quasiIso_of_locally
  intro U hyU
  obtain ⟨r,hr,hle,hsub⟩ := P.exists_restrictRadius_subset (U : Set X) (U.isOpen.mem_nhds hyU)
  let Q := P.restrictRadius r hr hle
  refine ⟨Q.openNeighborhood,Q.point_mem_neighborhood,hsub,?_⟩
  change QuasiIso (SingularSheafPullback.Constructions.singularOpenPreimageSheafMap (ModuleCat.of ℚ ℚ) f Q.openNeighborhood)
  exact normalPairSourceOpenSheafPullback_quasiIso Q hf

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSourceSheafComparison.Constructions
