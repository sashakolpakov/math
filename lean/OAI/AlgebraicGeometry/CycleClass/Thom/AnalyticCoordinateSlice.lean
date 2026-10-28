import OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential

/-! # Analytic Coordinate Slice -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticCoordinateSlice.Constructions

/-! Coordinate slices through the inverse of a holomorphic chart are holomorphic. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {N E F G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]

theorem inverse_chart_slice (P : OpenPartialHomeomorph N (E × F)) (U : Opens F)
    (hP : ContMDiffOn 𝓘(ℂ, E × F) 𝓘(ℂ, G) ω P.symm P.target)
    (hU : ∀ u : U, ((0 : E), u.val) ∈ P.target) :
    ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, G) ω (fun u : U => P.symm ((0 : E), u.val)) := by
  have hzero : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, E) ω (fun _ : U => (0 : E)) :=
    contMDiff_const
  have hval : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, F) ω (Subtype.val : U → F) :=
    contMDiff_subtype_val
  intro u
  exact ((hP ((0 : E), u.val) (hU u)).contMDiffAt (P.open_target.mem_nhds (hU u))).comp u
    (hzero.prodMk_space hval u)

end OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticCoordinateSlice.Constructions
