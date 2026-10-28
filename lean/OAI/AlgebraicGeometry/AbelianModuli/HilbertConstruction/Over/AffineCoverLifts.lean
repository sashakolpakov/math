import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.MorphismFactorization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverFactorization

/-! # Affine Cover Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.AffineCoverLifts

noncomputable section

/-! Unique factorizations through a relative monomorphism are
detected on the actual affine open cover of the test scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {X M : Over S} (j : X ⟶ M) [Mono j.left]
variable (T : Over S) (x : T ⟶ M)

def affineCoverOverMap (a : T.left.affineOpenCover.I₀) :
    Over.mk (T.left.affineOpenCover.f a ≫ T.hom) ⟶ T := Over.homMk (T.left.affineOpenCover.f a) rfl

theorem overUniqueLift_iff_affineOpenCover :
    (∃! y : T ⟶ X, y ≫ j = x) ↔
    ∀ a : T.left.affineOpenCover.I₀,
      ∃! y : Over.mk (T.left.affineOpenCover.f a ≫ T.hom) ⟶ X,
        y ≫ j = affineCoverOverMap T a ≫ x := by
  have : Mono j := Over.mono_of_mono_left _
  constructor
  · rintro ⟨y, hy, _⟩ a
    have he : (affineCoverOverMap T a ≫ y) ≫ j = affineCoverOverMap T a ≫ x := by
      rw [Category.assoc, hy]
    exact ⟨affineCoverOverMap T a ≫ y, he, fun z hz => (cancel_mono j).mp (hz.trans he.symm)⟩
  · intro H
    obtain ⟨g, hg, _⟩ := HilbertScheme.Presentations.Local.MorphismFactorization.lift_of_openCover T.left.affineOpenCover.openCover x.left j.left (by
      intro a
      obtain ⟨y, hy, _⟩ := H a
      exact ⟨y.left, congrArg Over.Hom.left hy⟩)
    let y := HilbertScheme.Presentations.OverFactorization.overHomOfFactorization g j x hg
    have hy : y ≫ j = x := HilbertScheme.Presentations.OverFactorization.overHomOfFactorization_comp _ _ _ hg
    exact ⟨y, hy, fun z hz => (cancel_mono j).mp (hz.trans hy.symm)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.AffineCoverLifts
