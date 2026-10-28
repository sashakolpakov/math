import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairSmoothSourceChart
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceRetraction
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential

/-! # Analytic Retraction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AnalyticRetraction.Constructions

noncomputable section

/-! The source retraction of an actual holomorphic normal pair is
holomorphic in the inherited native charts. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {M N E F G : Type} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace E M] [ChartedSpace G N]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x) (hf : Topology.IsEmbedding f)

theorem sourceHomeomorph_analytic
    (hfs : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω f)
    (hq : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E × F) ω P.ambientChart P.ambientChart.source) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentBallOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) ω).mp
  intro y
  have hy : f y.val ∈ P.ambientChart.source := P.neighborhood_subset_source y.property
  have hqAt := (hq (f y.val) hy).contMDiffAt (P.ambientChart.open_source.mem_nhds hy)
  have hc := hqAt.comp y ((hfs y.val).comp y contMDiff_subtype_val.contMDiffAt)
  change ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun y => (P.ambientChart (f y.val)).1) y
  exact ((ContinuousLinearMap.fst ℂ E F).contDiff (n := ω)).contMDiff.contMDiffAt.comp y hc

theorem sourceHomeomorph_symm_analytic
    (himm : ∀ y, Manifold.IsImmersionAt 𝓘(ℂ, E) 𝓘(ℂ, G) ω f y)
    (hqi : ContMDiffOn 𝓘(ℂ, E × F) 𝓘(ℂ, G) ω P.ambientChart.symm P.ambientChart.target) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P hf) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm ω).mp
  have he : f ∘ (Subtype.val ∘ (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm) =
      fun t => P.ambientChart.symm (t.val, (0 : F)) := by
    funext t
    exact HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceHomeomorph_inverse_inclusion P hf t
  have hs : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω
      (fun t : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentBallOpen P => P.ambientChart.symm (t.val, (0 : F))) := by
    intro t
    have ht : (t.val, (0 : F)) ∈ P.ambientChart.target :=
      P.product_subset_target ⟨t.property, Metric.mem_ball_self P.radius_pos⟩
    have hi := (hqi (t.val, 0) ht).contMDiffAt (P.ambientChart.open_target.mem_nhds ht)
    have hz : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E × F) ω
        (fun t : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentBallOpen P => (t.val, (0 : F))) :=
      (((ContinuousLinearMap.id ℂ E).prod (0 : E →L[ℂ] F)).contDiff (n := ω)).contMDiff.comp
        contMDiff_subtype_val
    exact hi.comp t (hz t)
  have hc : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω
      (f ∘ (Subtype.val ∘ (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm)) := he.symm ▸ hs
  intro t
  apply (ContMDiffAt.iff_comp_isImmersionAt (himm _)).mpr
  exact ⟨(continuous_subtype_val.comp (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf).symm.continuous).continuousAt, hc t⟩

variable {c d : ℕ} [ChartedSpace (Fin d → ℂ) M]
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x)

local instance : ChartedSpace G Q.neighborhood :=
  inferInstanceAs (ChartedSpace G Q.openNeighborhood)

local instance : ChartedSpace (Fin d → ℂ) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace Q) :=
  inferInstanceAs (ChartedSpace (Fin d → ℂ) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentBallOpen Q))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace E M] [TopologicalSpace M] [ChartedSpace (Fin d → ℂ) M] in
theorem tangentMap_analytic
    (hq : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ)) ω
      Q.ambientChart Q.ambientChart.source) :
    ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, Fin d → ℂ) ω (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentMap Q) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentBallOpen Q) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentMap Q) ω).mp
  intro y
  have hy := Q.neighborhood_subset_source y.property
  have hv : ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, G) ω (Subtype.val : Q.openNeighborhood → N) :=
    contMDiff_subtype_val
  have hc := ((hq y.val hy).contMDiffAt (Q.ambientChart.open_source.mem_nhds hy)).comp y
    (hv y)
  change ContMDiffAt 𝓘(ℂ, G) 𝓘(ℂ, Fin d → ℂ) ω (fun y => (Q.ambientChart y.val).1) y
  exact ((ContinuousLinearMap.fst ℂ (Fin d → ℂ) (Fin c → ℂ)).contDiff (n := ω)).contMDiff.contMDiffAt.comp y hc

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace E M] in
theorem retraction_analytic
    (himm : ∀ y, Manifold.IsImmersionAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, G) ω f y)
    (hq : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ)) ω
      Q.ambientChart Q.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ)) 𝓘(ℂ, G) ω
      Q.ambientChart.symm Q.ambientChart.target) :
    ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, Fin d → ℂ) ω (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap Q hf) :=
  (sourceHomeomorph_symm_analytic Q hf himm hqi).comp (tangentMap_analytic Q hq)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AnalyticRetraction.Constructions
