import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveChowModification
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Picard

/-! # Projective Modification -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent

noncomputable section

/-! The projective Chow modification detects isomorphism classes of line
bundles when the original proper integral scheme is normal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
variable {f : X ⟶ Spec (.of R)}

theorem ChowModificationModel.Construction.ChowModification.Model.picard_injective (D : ChowModificationModel.Construction.ChowModification.Model f)
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    Function.Injective (PicardPullbackId.Construction.PicardPullback.map D.projection) := by
  have : IsIntegral D.scheme := D.integral
  have : IsProper D.projection := D.proper
  have : Nonempty D.cover.common := D.cover.common_nonempty
  have : IsIso (D.projection ∣_ D.cover.common) := D.isIso_restrict
  exact Picard.Construction.PicardDescent.modification_injective D.projection hX D.cover.common

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent
