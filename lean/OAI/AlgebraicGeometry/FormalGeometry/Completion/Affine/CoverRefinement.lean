import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SiteDensity
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-! # Cover Refinement -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.CoverRefinement.Construction

noncomputable section

/-!
# Completion: finite affine refinements of actual covering sieves

Over an affine site object, quasi-compactness refines any actual covering
sieve to finitely many affine weakly étale maps lying in that sieve.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (U : X.ProEt)

/-- The member of an affine weakly étale cover as an object of the original site. -/
def affineRefinementSiteObject (V : Scheme.AffineCover.{u + 1} @WeaklyEtale U.left) (i : V.I₀) :
    X.ProEt := by
  have : WeaklyEtale (V.f i) := V.map_prop i
  exact Scheme.ProEt.mk (V.f i ≫ U.hom)

/-- The actual site morphism associated with an affine refinement member. -/
def affineRefinementSiteMap (V : Scheme.AffineCover.{u + 1} @WeaklyEtale U.left) (i : V.I₀) :
    affineRefinementSiteObject U V i ⟶ U :=
  MorphismProperty.Over.homMk (V.f i) rfl

/-- Any actual covering sieve over an affine object contains a finite affine covering family. -/
theorem proEtaleCoveringSieve_finiteAffineRefinement [IsAffine U.left]
    (sieve : Sieve U) (hs : sieve ∈ Scheme.ProEt.topology X U) :
    ∃ V : Scheme.AffineCover.{u + 1} @WeaklyEtale U.left,
      Finite V.I₀ ∧ ∀ i, sieve (affineRefinementSiteMap U V i) := by
  have : Precoverage.IsStableUnderComposition (Scheme.ProEt.precoverage X) :=
    inferInstanceAs (Precoverage.IsStableUnderComposition
      (Scheme.proetalePrecoverage.comap (Scheme.ProEt.forget X ⋙ Over.forget X)))
  have : Precoverage.IsStableUnderBaseChange (Scheme.ProEt.precoverage X) :=
    inferInstanceAs (Precoverage.IsStableUnderBaseChange
      (Scheme.proetalePrecoverage.comap (Scheme.ProEt.forget X ⋙ Over.forget X)))
  have : Precoverage.HasIsos (Scheme.ProEt.precoverage X) :=
    inferInstanceAs (Precoverage.HasIsos
      (Scheme.proetalePrecoverage.comap (Scheme.ProEt.forget X ⋙ Over.forget X)))
  obtain ⟨P, hP, hle⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hs
  obtain ⟨C, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hP
  let C' : U.left.Cover Scheme.proetalePrecoverage :=
    C.map (Scheme.ProEt.forget X ⋙ Over.forget X) (le_refl _)
  obtain ⟨V, r, hfin, _⟩ :
      ∃ (V : Scheme.AffineCover.{u + 1} @WeaklyEtale U.left) (r : V.cover ⟶ C'.forgetQc),
        Finite V.I₀ ∧ ∀ i, IsOpenImmersion (r.h₀ i) :=
    QuasiCompactCover.exists_hom C'.forgetQc
  refine ⟨V, hfin, fun i => ?_⟩
  let g : affineRefinementSiteObject U V i ⟶ C.X (r.s₀ i) :=
    MorphismProperty.Over.homMk (r.h₀ i) (by
      rw [← MorphismProperty.Over.w (C.f (r.s₀ i)), ← Category.assoc]
      change (r.h₀ i ≫ C'.forgetQc.f (r.s₀ i)) ≫ U.hom = V.f i ≫ U.hom
      rw [r.w₀]
      rfl)
  have hg : g ≫ C.f (r.s₀ i) = affineRefinementSiteMap U V i :=
    MorphismProperty.Over.Hom.ext (r.w₀ i)
  rw [← hg]
  exact sieve.downward_closed (hle _ _ ⟨r.s₀ i⟩) g

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.CoverRefinement.Construction
