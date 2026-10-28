import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceThomProjection
import OAI.AlgebraicTopology.Cohomology.Singular.Homotopy

/-! # Normal Pair Source Retraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceRetraction.Constructions

noncomputable section

/-! The genuine normal contraction retracts an immersion neighborhood onto its source slice. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.Homotopy

set_option backward.isDefEq.respectTransparency false

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {c d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)

def normalPairSourceRetractionHomotopy :
    TopCat.Homotopy (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf ≫ NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf)
      (𝟙 (TopCat.of P.neighborhood)) := by
  let e := NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P
  let H := CycleClass.Geometric.NormalProductPair.Cycles.normalConvexContraction (Fin c → ℂ) (Metric.ball 0 P.radius)
    (convex_ball 0 P.radius) (Metric.mem_ball_self P.radius_pos)
  exact {
    toFun := fun t => e.symm (H (t.1,(e t.2).1),(e t.2).2)
    continuous_toFun := e.symm.continuous.comp
      ((H.continuous.comp (continuous_fst.prodMk
        (continuous_fst.comp (e.continuous.comp continuous_snd)))).prodMk
        (continuous_snd.comp (e.continuous.comp continuous_snd)))
    map_zero_left := by
      intro y
      apply e.injective
      rw [e.apply_symm_apply]
      change (H (0,(e y).1),(e y).2) = _
      rw [show H (0,(e y).1) = ⟨0, Metric.mem_ball_self P.radius_pos⟩ from H.map_zero_left ((e y).1)]
      change (NormalPairProductSupport.Constructions.normalPairNormalOrigin P,(e y).2) =
        NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P
          (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf y))
      rw [NormalPairSourceSupport.Constructions.normalPairSourceInclusion_coordinates]
      change (NormalPairProductSupport.Constructions.normalPairNormalOrigin P,(e y).2) =
        (NormalPairProductSupport.Constructions.normalPairNormalOrigin P, NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf
          ((NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm ((e y).2)))
      rw [Homeomorph.apply_symm_apply]
    map_one_left := by
      intro y
      change e.symm (H (1,(e y).1),(e y).2) = y
      rw [show H (1,(e y).1) = (e y).1 from H.map_one_left ((e y).1)]
      exact e.symm_apply_apply y }

theorem normalPairSourceInclusion_retraction :
    NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf ≫ SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf =
      𝟙 (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  apply (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).injective
  change NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf
    ((NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm
      ((NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf y)).2)) =
    NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf y
  rw [Homeomorph.apply_symm_apply, NormalPairSourceSupport.Constructions.normalPairSourceInclusion_coordinates]

theorem normalPairSourceRetraction_cohomology (r : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) r) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf) r
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) r b) = b := by
  change (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) r ≫
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf) r) b = b
  rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp,
    AlgebraicTopology.Cohomology.Singular.Homotopy.singularCohomologyPullback_eq (ModuleCat.of ℚ ℚ) (normalPairSourceRetractionHomotopy P hf),
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id, ModuleCat.id_apply]

theorem normalPairSourceSupportedCohomologyIso_ambient_projection
    (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (q r : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ q)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) r) :
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K : Set P.neighborhood)ᶜ
      (Nat.add_assoc (2*c) q r)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of P.neighborhood)
        (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) K : Set P.neighborhood)ᶜ (2*c+q) r
        (SourceSupportedThomIso.Constructions.normalPairSourceSupportedCohomologyIso P hf K q a) b) =
    SourceSupportedThomIso.Constructions.normalPairSourceSupportedCohomologyIso P hf K (q+r)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))
        (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))ᶜ q r a
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) r b)) := by
  have h := SourceThomProjection.Constructions.normalPairSourceSupportedCohomologyIso_projection P hf K q r a
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) r b)
  rw [normalPairSourceRetraction_cohomology] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceRetraction.Constructions
