import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairReindex
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! # Smooth Normal Reindex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothNormalReindex.Constructions

noncomputable section

/-! Complex-linear normal reindexing preserves both smooth chart directions. -/

open scoped _root_.Manifold ContDiff

variable {M N E F G H : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [ChartedSpace H N]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
  (e : F ≃L[ℂ] G) (he : ∀ v, ‖e v‖ = ‖v‖)

theorem normalPairReindex_smooth
    (hq : ContMDiffOn 𝓘(ℂ, H) 𝓘(ℂ, E × F) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, E × F) 𝓘(ℂ, H) ∞ P.ambientChart.symm P.ambientChart.target) :
    ContMDiffOn 𝓘(ℂ, H) 𝓘(ℂ, E × G) ∞ (NormalPairReindex.Constructions.normalPairReindex P e he).ambientChart
      (NormalPairReindex.Constructions.normalPairReindex P e he).ambientChart.source ∧
    ContMDiffOn 𝓘(ℂ, E × G) 𝓘(ℂ, H) ∞ (NormalPairReindex.Constructions.normalPairReindex P e he).ambientChart.symm
      (NormalPairReindex.Constructions.normalPairReindex P e he).ambientChart.target := by
  let k := (ContinuousLinearEquiv.refl ℂ E).prodCongr e
  constructor
  · change ContMDiffOn _ _ ∞ (k ∘ P.ambientChart) P.ambientChart.source
    exact (k.contDiff (n := ∞)).contMDiff.comp_contMDiffOn hq
  · change ContMDiffOn _ _ ∞ (P.ambientChart.symm ∘ k.symm) (k.symm ⁻¹' P.ambientChart.target)
    exact hqi.comp (k.symm.contDiff (n := ∞)).contMDiff.contMDiffOn (fun _ hx => hx)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothNormalReindex.Constructions
