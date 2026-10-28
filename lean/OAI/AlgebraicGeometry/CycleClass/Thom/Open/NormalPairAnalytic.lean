import OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! # Normal Pair Analytic -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Open.NormalPairAnalytic.Constructions.Differentiable

/-! Normal charts extended from an actual ambient open subset remain
complex differentiable in both directions in the native induced atlas. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.PairTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section DomainRestriction

variable {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]

theorem mdifferentiableAt_domainSubtype_iff (U : Opens M) (f : M → N) (x : U) :
    MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) (fun z : U => f z.val) x ↔
      MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x.val :=
  (differentiableWithinAt_localInvariantProp.liftPropAt_iff_comp_subtype_val _ _).symm

end DomainRestriction

variable {N E F G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  (U : Opens N)

theorem openChart_lift_mdifferentiable
    (P : OpenPartialHomeomorph U (E × F))
    (hP : P.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F)) :
    (P.lift_openEmbedding U.isOpenEmbedding').MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F) := by
  constructor
  · rintro _ ⟨z, hz, rfl⟩
    have h : MDifferentiableAt 𝓘(ℂ, G) 𝓘(ℂ, E × F)
        (fun v : U => (P.lift_openEmbedding U.isOpenEmbedding') v.val) z := by
      simpa only [OpenPartialHomeomorph.lift_openEmbedding_apply] using hP.mdifferentiableAt hz
    exact ((mdifferentiableAt_domainSubtype_iff U (P.lift_openEmbedding U.isOpenEmbedding') z).mp h).mdifferentiableWithinAt
  · intro z hz
    change MDifferentiableWithinAt 𝓘(ℂ, E × F) 𝓘(ℂ, G) (Subtype.val ∘ P.symm) P.target z
    have hv : MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, G) (Subtype.val : U → N) :=
      (contMDiff_subtype_val (n := 1)).mdifferentiable one_ne_zero
    exact hv.mdifferentiableAt.comp_mdifferentiableWithinAt z (hP.2 z hz)

theorem openTransportNormalPair_mdifferentiable {M : Type} {f : M → U} {x : M}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F)) :
    (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair P Subtype.val U.isOpenEmbedding').ambientChart.MDifferentiable
      𝓘(ℂ, G) 𝓘(ℂ, E × F) :=
  openChart_lift_mdifferentiable U P.ambientChart hP

end AlgebraicGeometry.CycleClass.Thom.Open.NormalPairAnalytic.Constructions.Differentiable

namespace AlgebraicGeometry.CycleClass.Thom.Open.NormalPairAnalytic.Constructions

/-! The actual native extension of a normal chart from an ambient
open subset is holomorphic in both directions. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.PairTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N E F G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  (U : Opens N)

theorem openChart_lift_analytic (P : OpenPartialHomeomorph U (E × F))
    (hP : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E × F) ω P P.source) :
    ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E × F) ω
      (P.lift_openEmbedding U.isOpenEmbedding') (P.lift_openEmbedding U.isOpenEmbedding').source := by
  rintro _ ⟨z, hz, rfl⟩
  have h : ContMDiffAt 𝓘(ℂ, G) 𝓘(ℂ, E × F) ω
      (fun v : U => (P.lift_openEmbedding U.isOpenEmbedding') v.val) z := by
    simpa only [OpenPartialHomeomorph.lift_openEmbedding_apply] using
      (hP z hz).contMDiffAt (P.open_source.mem_nhds hz)
  exact (contMDiffAt_subtype_iff.mp h).contMDiffWithinAt

theorem openChart_lift_symm_analytic (P : OpenPartialHomeomorph U (E × F))
    (hP : ContMDiffOn 𝓘(ℂ, E × F) 𝓘(ℂ, G) ω P.symm P.target) :
    ContMDiffOn 𝓘(ℂ, E × F) 𝓘(ℂ, G) ω
      (P.lift_openEmbedding U.isOpenEmbedding').symm (P.lift_openEmbedding U.isOpenEmbedding').target :=
  (contMDiff_subtype_val (I := 𝓘(ℂ, G)) (n := ω)).comp_contMDiffOn hP

theorem openTransportNormalPair_analytic {M : Type} {f : M → U} {x : M}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hP : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E × F) ω P.ambientChart P.ambientChart.source) :
    ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E × F) ω
      (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair P Subtype.val U.isOpenEmbedding').ambientChart
      (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair P Subtype.val U.isOpenEmbedding').ambientChart.source :=
  openChart_lift_analytic U P.ambientChart hP

theorem openTransportNormalPair_symm_analytic {M : Type} {f : M → U} {x : M}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hP : ContMDiffOn 𝓘(ℂ, E × F) 𝓘(ℂ, G) ω P.ambientChart.symm P.ambientChart.target) :
    ContMDiffOn 𝓘(ℂ, E × F) 𝓘(ℂ, G) ω
      (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair P Subtype.val U.isOpenEmbedding').ambientChart.symm
      (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair P Subtype.val U.isOpenEmbedding').ambientChart.target :=
  openChart_lift_symm_analytic U P.ambientChart hP

end AlgebraicGeometry.CycleClass.Thom.Open.NormalPairAnalytic.Constructions

end

end OAI
