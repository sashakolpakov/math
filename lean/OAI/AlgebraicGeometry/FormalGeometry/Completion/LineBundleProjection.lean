import OAI.AlgebraicGeometry.Quotients.FiniteDescent.MonoidalLine
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvertibleProjectionTensor

/-! # Line Bundle Projection -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundleProjection.Construction

noncomputable section

/-! The actual projection formula for right tensoring by a line bundle,
deduced from tensor invertibility and the pullback/direct-image adjunction. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory MonoidalCategory

universe u

attribute [local instance] SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory SheafCohomology.Projective.Monoidal.Scheme.Modules.symmetricCategory

def lineBundleProjectionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (M : X.Modules) :
    (Scheme.Modules.pushforward f).obj M ⊗ L.sheaf ≅
      (Scheme.Modules.pushforward f).obj (M ⊗ (L.pullback f).sheaf) := by
  let := SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  exact (β_ ((Scheme.Modules.pushforward f).obj M) L.sheaf) ≪≫
    Quotients.FiniteDescent.InvertibleProjectionTensor.Construction.InvertibleProjection.iso (Scheme.Modules.pullback f) (Scheme.Modules.pushforward f)
      (Scheme.Modules.pullbackPushforwardAdjunction f) L.sheaf (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L).sheaf
      (Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.evaluation L) (Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.evaluation_swap L) M ≪≫
    (Scheme.Modules.pushforward f).mapIso (β_ (L.pullback f).sheaf M)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundleProjection.Construction
