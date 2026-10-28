import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairProductSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ImmersionSmoothPullback
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothOpenChartTrace

/-! # Pair Smooth Source Chart -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairSmoothSourceChart.Constructions

noncomputable section

/-! The actual tangent chart of a smooth embedded normal pair is a complex diffeomorphism. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {M N E F G : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace E M] [ChartedSpace G N]
variable {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x) (hf : Topology.IsEmbedding f)

theorem normalPairSourceHomeomorph_contMDiff
    (hfs : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ∞ f)
    (hq : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E × F) ∞ P.ambientChart P.ambientChart.source) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) := by
  apply (ContMDiff.subtypeVal_comp_iff (NormalPairProductSupport.Constructions.normalPairTangentBallOpen P) (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf)).mp
  intro y
  have hy : f y.val ∈ P.ambientChart.source := P.neighborhood_subset_source y.property
  have hqAt := (hq (f y.val) hy).contMDiffAt (P.ambientChart.open_source.mem_nhds hy)
  have hc := hqAt.comp y ((hfs y.val).comp y contMDiff_subtype_val.contMDiffAt)
  change ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (fun y => (P.ambientChart (f y.val)).1) y
  exact ((ContinuousLinearMap.fst ℂ E F).contDiff (n := ∞)).contMDiff.contMDiffAt.comp y hc

theorem normalPairSourceHomeomorph_symm_contMDiff
    (himm : ∀ y, Manifold.IsImmersionAt 𝓘(ℂ, E) 𝓘(ℂ, G) ∞ f y)
    (hqi : ContMDiffOn 𝓘(ℂ, E × F) 𝓘(ℂ, G) ∞ P.ambientChart.symm P.ambientChart.target) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm := by
  apply (ContMDiff.subtypeVal_comp_iff (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf) (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm).mp
  have he : f ∘ (Subtype.val ∘ (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm) =
      fun t => P.ambientChart.symm (t.val, (0 : F)) := by
    funext t
    exact NormalPairProductSupport.Constructions.normalPairSourceHomeomorph_inverse_inclusion P hf t
  have hs : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ∞
      (fun t : NormalPairProductSupport.Constructions.normalPairTangentBallOpen P => P.ambientChart.symm (t.val, (0 : F))) := by
    intro t
    have ht : (t.val,(0 : F)) ∈ P.ambientChart.target :=
      P.product_subset_target ⟨t.property,Metric.mem_ball_self P.radius_pos⟩
    have hi := (hqi (t.val,0) ht).contMDiffAt (P.ambientChart.open_target.mem_nhds ht)
    have hz : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E × F) ∞
        (fun t : NormalPairProductSupport.Constructions.normalPairTangentBallOpen P => (t.val, (0 : F))) :=
      (((ContinuousLinearMap.id ℂ E).prod (0 : E →L[ℂ] F)).contDiff (n := ∞)).contMDiff.comp
        contMDiff_subtype_val
    exact hi.comp t (hz t)
  have hc : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ∞
      (f ∘ (Subtype.val ∘ (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm)) := he.symm ▸ hs
  intro t
  apply (ContMDiffAt.iff_comp_isImmersionAt (himm _)).mpr
  exact ⟨(continuous_subtype_val.comp (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm.continuous).continuousAt, hc t⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairSmoothSourceChart.Constructions
