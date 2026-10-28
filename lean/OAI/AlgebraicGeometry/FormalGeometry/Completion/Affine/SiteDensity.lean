import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.ProEtaleRepresentation
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-! # Site Density -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SiteDensity.Construction

noncomputable section

/-!
# Completion: affine spectra cover the actual pro-étale site

Every site object has its ordinary affine open cover, and every member
is recovered from its coordinate algebra by the checked spectrum isomorphism.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (U : X.ProEt)

/-- An affine open of a site object is again an actual site object. -/
def proEtaleAffineOpen (i : U.left.affineCover.I₀) : X.ProEt :=
  Scheme.ProEt.mk (U.left.affineCover.f i ≫ U.hom)

/-- The inclusion of an affine open in the actual site. -/
def proEtaleAffineOpenInclusion (i : U.left.affineCover.I₀) : proEtaleAffineOpen U i ⟶ U :=
  MorphismProperty.Over.homMk (U.left.affineCover.f i) rfl

instance (i : U.left.affineCover.I₀) : IsAffine (proEtaleAffineOpen U i).left :=
  inferInstanceAs (IsAffine (U.left.affineCover.X i))

/-- The ordinary affine open cover is a covering family in the actual site. -/
theorem proEtaleAffineOpen_cover :
    Sieve.generate (Presieve.ofArrows (proEtaleAffineOpen U) (proEtaleAffineOpenInclusion U)) ∈
      Scheme.ProEt.topology X U := by
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.ofArrows (proEtaleAffineOpen U) (proEtaleAffineOpenInclusion U)).map
    (Scheme.ProEt.forget X ⋙ Over.forget X) ∈ Scheme.proetalePrecoverage U.left
  rw [Presieve.map_ofArrows]
  exact Scheme.zariskiPrecoverage_le_propQCPrecoverage _ U.left.affineCover.mem₀

/-- Actual weakly étale affine algebras form a cover-dense subcategory of the site. -/
theorem proEtaleAlgebraSpecCoverDense (R : Type u) [CommRing R] :
    (ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).IsCoverDense (Scheme.ProEt.topology (Spec (CommRingCat.of R))) where
  is_cover U := by
    apply (Scheme.ProEt.topology (Spec (CommRingCat.of R))).superset_covering
      ((Sieve.generate_le_iff _ _).mpr ?_) (proEtaleAffineOpen_cover U)
    intro V g hg
    cases hg with
    | mk i =>
      let e := ProEtaleRepresentation.Construction.proEtaleAlgebraOfAffineIso (proEtaleAffineOpen U i)
      exact ⟨⟨op (ProEtaleRepresentation.Construction.proEtaleAlgebraOfAffine (proEtaleAffineOpen U i)), e.inv,
        e.hom ≫ proEtaleAffineOpenInclusion U i, by simp⟩⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SiteDensity.Construction
