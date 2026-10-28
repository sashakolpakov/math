import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation

/-! # Line Bundle Free -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence

noncomputable section

/-! Actual rank-one frames provide the quasicoherence and finite
presentation required by the cohomology construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

universe u

variable {X : Scheme.{u}}

theorem invertible (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible L.sheaf := by
  choose U hx he using L.locallyTrivial
  refine ⟨X, U, ?_, he⟩
  apply top_unique
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩

theorem finitePresentation (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : L.sheaf.IsFinitePresentation :=
  SheafCohomology.Projective.InvertibleFinitePresentation.invertible_finitePresentation (invertible L)

theorem locallyFree (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : L.sheaf.IsLocallyFree :=
  (SheafCohomology.Projective.InvertibleFinitePresentation.rankOneCoverLocalGenerators
    (SheafCohomology.Projective.InvertibleFinitePresentation.invertibleRankOneCover (invertible L))).isLocallyFree

theorem quasicoherent (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : L.sheaf.IsQuasicoherent :=
  SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent (invertible L)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence
