import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.Modification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveProducts

/-! # Projective Chow Modification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Proper integral schemes over affine bases admit actual projective modifications. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}

theorem Chow.Modification.ChowModification.Model.coverIndex_nonempty (D : Chow.Modification.ChowModification.Model f) : Nonempty (Fin D.cover.n) := by
  obtain ⟨x⟩ := D.cover.common_nonempty
  obtain ⟨i, _⟩ := D.cover.covers x.val
  exact ⟨i⟩

def Chow.Modification.ChowModification.Model.productProjectivePresentation (D : Chow.Modification.ChowModification.Model f) :
    Projective.ProjectivePresentations.ProjectivePresentation (∏ᶜ (fun i => Over.mk (D.compactification i).base)) := by
  have : Nonempty (Fin D.cover.n) := D.coverIndex_nonempty
  exact Finite.ProjectiveProducts.overFinProductPresentation D.cover.n _
    (fun i => (D.compactification i).projectivePresentation)

def Chow.Modification.ChowModification.Model.projectivePresentation (D : Chow.Modification.ChowModification.Model f) :
    Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (D.projection ≫ f)) := by
  let j : Over.mk (D.projection ≫ f) ⟶
      ∏ᶜ (fun i => Over.mk (D.compactification i).base) :=
    Over.homMk D.embedding D.embedding_base
  have : IsClosedImmersion j.left := D.closedImmersion
  exact D.productProjectivePresentation.ofClosedImmersion j

theorem Projective.ProjectiveChowModification.ChowModification.exists_projective_modification [IsIntegral X]
    (f : X ⟶ Spec (.of R)) [IsProper f] :
    ∃ (Z : Scheme.{u}) (_ : IsIntegral Z) (q : Z ⟶ X),
      IsProper q ∧ Surjective q ∧
      (∃ U : X.Opens, Nonempty U ∧ IsAffineOpen U ∧ IsIso (q ∣_ U)) ∧
      Nonempty (Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (q ≫ f))) := by
  let D := Chow.Modification.ChowModification.build f
  exact ⟨D.scheme, D.integral, D.projection, D.proper, D.surjective,
    ⟨D.cover.common, D.cover.common_nonempty, D.cover.common_affine, D.isIso_restrict⟩,
    ⟨D.projectivePresentation⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
