import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LineBundleImage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.GenericLine

/-! # Line Quasicoherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow

noncomputable section

/-! The actual line bundles on the Chow model have quasicoherent direct images on the original scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}

theorem Modification.ChowModification.Model.lineBundlePushforward_quasicoherent (D : Modification.ChowModification.Model f) (L : Line.Bundles.LineBundle D.scheme) :
    ((Scheme.Modules.pushforward D.projection).obj L.sheaf).IsQuasicoherent := by
  have : IsProper D.projection := D.proper
  exact Proper.LineBundleImage.proper_lineBundle_directImage_quasicoherent D.projection L

theorem Modification.ChowModification.Model.amplePowerPushforward_quasicoherent (D : Modification.ChowModification.Model f) (n : ℕ) :
    ((Scheme.Modules.pushforward D.projection).obj (D.ampleLineBundle.tensorPower n).sheaf).IsQuasicoherent :=
  D.lineBundlePushforward_quasicoherent (D.ampleLineBundle.tensorPower n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow
