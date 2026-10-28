import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChowAmpleLine
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.LinePushforward

/-! # Chow Line Pushforward -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChowLinePushforward

noncomputable section

/-! The actual line bundles on a constructed Chow modification have
coherent direct images on its proper integral target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem chowLinePushforward_finiteType
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]
    (D : Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.Model f) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle D.scheme) :
    ((Scheme.Modules.pushforward D.projection).obj L.sheaf).IsFiniteType := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsProper D.projection := D.proper
  exact Projective.LinePushforward.lineBundlePushforward_finiteType_of_relativelyAmple D.projection
    (ChowAmpleLine.chowAmpleLine D) (ChowAmpleLine.chowAmpleLine_relative_to_target D) L

theorem chowLinePushforward_quasicoherent
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} (D : Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.Model f) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle D.scheme) :
    ((Scheme.Modules.pushforward D.projection).obj L.sheaf).IsQuasicoherent := by
  have : IsProper D.projection := D.proper
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  exact QuasicoherentPushforward.quasicoherent_pushforward_of_quasiCompact_separated D.projection L.sheaf

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChowLinePushforward
