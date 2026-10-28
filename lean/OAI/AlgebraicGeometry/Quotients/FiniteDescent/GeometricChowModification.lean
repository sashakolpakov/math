import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveChowModification
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricModificationIntegral

/-! # Geometric Chow Modification -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent

noncomputable section

/-! Chow modifications of a proper geometrically integral scheme over a
field retain geometric integrality. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of K)) [IsProper f] [GeometricallyIntegral f]

theorem ChowModificationModel.Construction.ChowModification.Model.geometricallyIntegral (D : ChowModificationModel.Construction.ChowModification.Model f) : GeometricallyIntegral (D.projection ≫ f) := by
  have : IsIntegral D.scheme := D.integral
  have : IsProper D.projection := D.proper
  have : Surjective D.projection := D.surjective
  have : Nonempty D.cover.common := D.cover.common_nonempty
  have : IsIso (D.projection ∣_ D.cover.common) := D.isIso_restrict
  exact GeometricModificationIntegral.Construction.GeometricModification.geometricallyIntegral f D.projection D.cover.common

theorem GeometricChowModification.Construction.ChowModification.exists_geometric_projective_modification :
    ∃ (Z : Scheme.{u}) (_ : IsIntegral Z) (q : Z ⟶ X),
      IsProper q ∧ Surjective q ∧ GeometricallyIntegral (q ≫ f) ∧
      (∃ U : X.Opens, Nonempty U ∧ IsAffineOpen U ∧ IsIso (q ∣_ U)) ∧
      Nonempty (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (q ≫ f))) := by
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  let D := ChowModificationModel.Construction.ChowModification.build f
  exact ⟨D.scheme, D.integral, D.projection, D.proper, D.surjective, D.geometricallyIntegral f,
    ⟨D.cover.common, D.cover.common_nonempty, D.cover.common_affine, D.isIso_restrict⟩,
    ⟨D.projectivePresentation⟩⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent
