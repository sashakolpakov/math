import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveRenaming
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.GrassmannianProjectivity
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Has

/-! # Projective Coordinate Iso -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.ProjectiveCoordinateIso.PolynomialProjective

noncomputable section

/-! Reindexing a finite projective coordinate set produces the exact
relative projective space used by the Presentations statement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {σ : Type u} {d : ℕ} (S : Scheme.{u}) (e : σ ≃ Fin (d + 1))

def relativeProjectiveCoordinateMap : GrassmannianProjectivity.PolynomialProjective.relativeProjectiveSpace σ S ⟶ Has.Core.projectiveSpace S d :=
  pullback.map (Projective.Flatness.GradedHilbert.projectiveStructureMap (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ Γ(S, ⊤))) S.toSpecΓ
    (Has.Core.projectiveSpaceMap Γ(S, ⊤) d) S.toSpecΓ
    (Polynomial.ProjectiveRenaming.PolynomialProjective.polynomialProjectiveCoordinateIso (R := Γ(S, ⊤)) e).hom (𝟙 S) (𝟙 _)
    (by rw [Category.comp_id]; exact (Polynomial.ProjectiveRenaming.PolynomialProjective.polynomialProjectiveCoordinateIso_over e).symm)
    (by rw [Category.comp_id, Category.id_comp])

instance relativeProjectiveCoordinateMap_isIso : IsIso (relativeProjectiveCoordinateMap S e) := by
  unfold relativeProjectiveCoordinateMap
  exact pullback.map_isIso _ _ _ _ _ _ _ _ _

def relativeProjectiveCoordinateIso : GrassmannianProjectivity.PolynomialProjective.relativeProjectiveSpace σ S ≅ Has.Core.projectiveSpace S d :=
  asIso (relativeProjectiveCoordinateMap S e)

theorem relativeProjectiveCoordinateIso_over :
    (relativeProjectiveCoordinateIso S e).hom ≫ Has.Core.projectiveSpaceProjection S d =
      GrassmannianProjectivity.PolynomialProjective.relativeProjectiveSpaceProjection σ S := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.ProjectiveCoordinateIso.PolynomialProjective
