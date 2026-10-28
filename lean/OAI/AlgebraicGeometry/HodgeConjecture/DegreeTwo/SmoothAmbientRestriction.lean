import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Complex.Basic
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairAmbientRestriction
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Smooth Ambient Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothAmbientRestriction.Constructions

noncomputable section

/-!
# DegreeTwo: smooth native normal charts restrict to ambient opens

Restriction uses the actual induced manifold on the open subtype. The
inverse chart remains smooth because its composite with the inclusion
agrees with the original inverse on the entire restricted target.
-/

open _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable {N G E : Type*} [TopologicalSpace N]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Both directions of a smooth native chart remain smooth on an actual
ambient open subtype. -/
theorem contMDiffOn_subtypeRestr (q : OpenPartialHomeomorph N E)
    (hq : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E) ∞ q q.source)
    (hqi : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, G) ∞ q.symm q.target)
    (U : Opens N) (hU : Nonempty U) :
    ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E) ∞ (q.subtypeRestr hU) (q.subtypeRestr hU).source ∧
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, G) ∞ (q.subtypeRestr hU).symm (q.subtypeRestr hU).target := by
  constructor
  · rw [q.subtypeRestr_source]
    change ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E) ∞ (q ∘ (Subtype.val : U → N))
      ((Subtype.val : U → N) ⁻¹' q.source)
    exact hq.comp contMDiff_subtype_val.contMDiffOn (fun _ hx => hx)
  · have hcomp : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, G) ∞
        (Subtype.val ∘ (q.subtypeRestr hU).symm) (q.subtypeRestr hU).target := by
      apply (hqi.mono (q.subtypeRestr_target_subset hU)).congr
      intro z hz
      exact q.subtypeRestr_symm_apply hU hz
    intro z hz
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U (q.subtypeRestr hU).symm
      (q.subtypeRestr hU).target z).mp (hcomp z hz)

theorem normalPairRestrictAmbient_mdifferentiable
    {M F : Type} {N G E : Type} [TopologicalSpace N]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (U : Opens N) (hPU : P.neighborhood ⊆ U)
    (hq : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E × F) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, E × F) 𝓘(ℂ, G) ∞ P.ambientChart.symm P.ambientChart.target) :
    (NormalPairAmbientRestriction.Constructions.normalPairRestrictAmbient P U hPU).ambientChart.MDifferentiable
      𝓘(ℂ, G) 𝓘(ℂ, E × F) := by
  have h := contMDiffOn_subtypeRestr P.ambientChart hq hqi U
    ⟨⟨f x, hPU P.point_mem_neighborhood⟩⟩
  exact ⟨h.1.mdifferentiableOn (by simp), h.2.mdifferentiableOn (by simp)⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothAmbientRestriction.Constructions
