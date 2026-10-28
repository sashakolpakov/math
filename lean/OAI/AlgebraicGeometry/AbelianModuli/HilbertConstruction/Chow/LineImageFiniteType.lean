import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralImageFiniteType
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.LineQuasicoherence

/-! # Line Image Finite Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow

noncomputable section

/-! Line bundles on the actual Chow modification have quasicoherent finite-type direct images on the original Noetherian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]

theorem Modification.ChowModification.Model.lineBundlePushforward_finiteType (D : Modification.ChowModification.Model f) (L : Line.Bundles.LineBundle D.scheme) :
    ((Scheme.Modules.pushforward D.projection).obj L.sheaf).IsFiniteType := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsIntegral D.scheme := D.integral
  have : IsProper D.projection := D.proper
  have : Surjective D.projection := D.surjective
  exact Proper.IntegralImageFiniteType.proper_surjective_integral_lineBundle_directImage_finiteType D.projection L

theorem Modification.ChowModification.Model.amplePowerPushforward_finiteType (D : Modification.ChowModification.Model f) (n : ℕ) :
    ((Scheme.Modules.pushforward D.projection).obj (D.ampleLineBundle.tensorPower n).sheaf).IsFiniteType :=
  D.lineBundlePushforward_finiteType (D.ampleLineBundle.tensorPower n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow
