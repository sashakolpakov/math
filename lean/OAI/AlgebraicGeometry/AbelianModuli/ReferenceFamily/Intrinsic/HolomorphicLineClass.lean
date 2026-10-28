import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.LogUnitClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.ChernComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RegularEvaluation

/-! # Holomorphic Line Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass

noncomputable section

/-! An arbitrary actual algebraic line bundle gives a class in the
native holomorphic unit-sheaf cohomology. Its transitions are the
original regular frame units, and its logarithms are the original
ones used to define the native Chern class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RegularEvaluation
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem frameTransitionPair_holomorphic {M : V.carrier.Modules} (s t : LineFrameAtlas.LocalLineFrame M) :
    ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ) ∞ (AnalyticFrameTransitions.frameTransitionPair V.presentation s t) := by
  let W : V.carrier.Opens := s.domain ⊓ t.domain
  let u : Γ(V.carrier, W) := (s.transition t W inf_le_left inf_le_right).val
  have hf := (DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V W u).property
  apply hf.congr
  intro x
  rfl

variable (L : HilbertConstruction.Line.Bundles.LineBundle V.carrier)

theorem nativeBundleLogCech_holomorphic
    (a : Fin 2 → (ChernClasses.nativeLineBundle V.presentation L).LogCoverIndex) :
    ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ) ∞
      ((ChernClasses.nativeLineBundle V.presentation L).bundleLogCech a) := by
  let B := ChernClasses.nativeLineBundle V.presentation L
  let U := B.logCover
  let r := Frame.ChernComparison.chosenLineFrame B (B.logParent (a 0))
  let t := Frame.ChernComparison.chosenLineFrame B (B.logParent (a 1))
  have ha : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a ≤ AnalyticFrameTransitions.frameAnalyticOpen V.presentation r ⊓
      AnalyticFrameTransitions.frameAnalyticOpen V.presentation t :=
    le_inf ((AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0).trans (B.logCover_subset (a 0)))
      ((AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1).trans (B.logCover_subset (a 1)))
  let f : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :=
    ⟨fun x => AnalyticFrameTransitions.frameTransitionPair V.presentation r t (Opens.inclusion ha x),
      (frameTransitionPair_holomorphic V r t).comp (contMDiff_inclusion ha)⟩
  apply DivisorClass.Chern.ContinuousHolomorphicLog.continuous_logarithm_holomorphic f (B.bundleLogCech a)
  intro x
  exact (B.bundleLogCech_exp_point a x).trans
    (Frame.ChernComparison.chosenLineFrame_transition B (B.logParent (a 0)) (B.logParent (a 1)) x.val
      (B.logCover_subset (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
      (B.logCover_subset (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property))).symm

def nativeHolomorphicLineClass : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace :=
  Holomorphic.LogUnitClass.holomorphicLogUnitClass V.analyticModel V.analyticSpace
    (ChernClasses.nativeLineBundle V.presentation L).logCover (ChernClasses.nativeLineBundle V.presentation L).bundleLogCech
    (nativeBundleLogCech_holomorphic V L) (ChernClasses.nativeLineBundle V.presentation L).bundleLogCech_cocycle
    (ChernClasses.nativeLineBundle V.presentation L).logCover_covers

theorem nativeHolomorphicLineClass_transition
    (a : Fin 2 → (ChernClasses.nativeLineBundle V.presentation L).LogCoverIndex)
    (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (ChernClasses.nativeLineBundle V.presentation L).logCover a) :
    (Holomorphic.LogUnitClass.holomorphicUnitSection V.analyticModel V.analyticSpace
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (ChernClasses.nativeLineBundle V.presentation L).logCover a)
      (Holomorphic.LogUnitClass.holomorphicLogUnitCech V.analyticModel V.analyticSpace
      (ChernClasses.nativeLineBundle V.presentation L).logCover (ChernClasses.nativeLineBundle V.presentation L).bundleLogCech
      (nativeBundleLogCech_holomorphic V L) a)).val x =
    (ChernClasses.nativeLineBundle V.presentation L).pointTransition
      ((ChernClasses.nativeLineBundle V.presentation L).logParent (a 0))
      ((ChernClasses.nativeLineBundle V.presentation L).logParent (a 1)) x.val
      ((ChernClasses.nativeLineBundle V.presentation L).logCover_subset (a 0)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0 x.property))
      ((ChernClasses.nativeLineBundle V.presentation L).logCover_subset (a 1)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1 x.property)) :=
  (ChernClasses.nativeLineBundle V.presentation L).bundleLogCech_exp_point a x

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass
