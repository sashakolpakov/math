import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-! # Morphism Property Open Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.MorphismPropertyOpenDescent

noncomputable section

/-! A target-local property of an over-scheme morphism can be checked
on the native pullbacks to an open cover of its base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} {X Y : Over S}

theorem overMorphism_property_of_openCover
    (f : X ⟶ Y) (U : S.OpenCover.{u})
    (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Q]
    (hQ : ∀ i, Q ((Over.pullback (U.f i)).map f).left) : Q f.left := by
  apply IsZariskiLocalAtTarget.of_openCover (U.pullback₁ Y.hom)
  intro i
  let H := Projective.PresentationBaseChange.overPullback_map_isPullback f (U.f i)
  let e : Arrow.mk ((Over.pullback (U.f i)).map f).left ≅
      Arrow.mk (pullback.snd f.left (pullback.fst Y.hom (U.f i))) :=
    Arrow.isoMk H.isoPullback (Iso.refl _) (by
      change H.isoPullback.hom ≫ pullback.snd f.left (pullback.fst Y.hom (U.f i)) =
        ((Over.pullback (U.f i)).map f).left ≫ 𝟙 _
      exact H.isoPullback_hom_snd.trans (Category.comp_id _).symm)
  exact (Q.arrow_mk_iso_iff e).mp (hQ i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.MorphismPropertyOpenDescent
