import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.ProjectiveCoordinateIso

/-! # Coordinate Projective Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoordinateProjectivePresentation.PolynomialProjective

noncomputable section

/-! A closed embedding in relative projective space with an arbitrary
nonempty finite coordinate set gives the exact Presentations projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {σ : Type u} [Fintype σ] [Nonempty σ]

def projectivePresentationOfFiniteCoordinates (X : Over S)
    (i : X.left ⟶ Relative.GrassmannianProjectivity.PolynomialProjective.relativeProjectiveSpace σ S) [IsClosedImmersion i]
    (hi : i ≫ Relative.GrassmannianProjectivity.PolynomialProjective.relativeProjectiveSpaceProjection σ S = X.hom) : Has.Core.ProjectivePresentation X := by
  let d := Fintype.card σ - 1
  have hc : Fintype.card σ = d + 1 := (Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)).symm
  let e : σ ≃ Fin (d + 1) := Fintype.equivFinOfCardEq hc
  refine ⟨d, i ≫ (Relative.ProjectiveCoordinateIso.PolynomialProjective.relativeProjectiveCoordinateIso S e).hom, inferInstance, ?_⟩
  rw [Category.assoc, Relative.ProjectiveCoordinateIso.PolynomialProjective.relativeProjectiveCoordinateIso_over]
  exact hi

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoordinateProjectivePresentation.PolynomialProjective
