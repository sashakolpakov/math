import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.Neighborhoods
import OAI.AlgebraicGeometry.FormalGeometry.Completion.QuotientPushout
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Infinitesimal Sections -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.InfinitesimalSections.Construction

noncomputable section

/-! Actual sections on affine charts of the infinitesimal neighborhoods are
the quotients of the original chart rings by the extended ideal powers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The literal base-ring map on an open chart. -/
def baseOpenSectionsMap (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U (by simp)).hom

/-- The base quotient acts on sections of the actual infinitesimal chart. -/
def infinitesimalOpenBaseSectionsMap (n : ℕ) (U : X.Opens) :
    CommRingCat.of (R ⧸ I ^ (n + 1)) ⟶
      Γ(Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood I f n, pullback.fst f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U) :=
  (Scheme.ΓSpecIso (.of (R ⧸ I ^ (n + 1)))).inv ≫
    (pullback.snd f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)).appLE ⊤ _ (by simp)

/-- Affine chart base change gives the actual quotient pushout square. -/
theorem affineInfinitesimalSections_isPushout (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (baseOpenSectionsMap f U))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))
      ((pullback.fst f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)).app U)
      (infinitesimalOpenBaseSectionsMap I f n U) := by
  have : IsAffine (Infinitesimal.Neighborhoods.Construction.infinitesimalBase I n) := inferInstanceAs (IsAffine (Spec _))
  have hs := isIso_pushoutSection_of_isAffineOpen
    (IsPullback.of_hasPullback f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n))
    (US := ⊤) (UT := ⊤) (UX := U)
    (UY := pullback.fst f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U)
    (by simp) (by simp) (by simp) (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hp := (isIso_pushoutSection_iff
    (IsPullback.of_hasPullback f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n))
    (US := ⊤) (UT := ⊤) (UX := U)
    (UY := pullback.fst f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U)
    (by simp) (by simp) (by simp)).mp hs
  apply hp.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _)
    (Scheme.ΓSpecIso (.of (R ⧸ I ^ (n + 1)))) (Iso.refl _)
  · simp [baseOpenSectionsMap]
  · change (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n).appTop ≫ (Scheme.ΓSpecIso _).hom =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))
    exact Scheme.ΓSpecIso_naturality _
  · simp [Scheme.Hom.app_eq_appLE]
  · simp [infinitesimalOpenBaseSectionsMap]

/-- The quotient of the actual chart ring is its actual infinitesimal section ring. -/
def affineInfinitesimalSectionsIso (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U) :
    CommRingCat.of (Γ(X, U) ⧸ (I ^ (n + 1)).map (baseOpenSectionsMap f U)) ≅
      Γ(Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood I f n, pullback.fst f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U) :=
  QuotientPushout.Construction.quotientPushoutIso (baseOpenSectionsMap f U) (I ^ (n + 1))
    (affineInfinitesimalSections_isPushout I f n U hU)

theorem affineInfinitesimalSectionsIso_mk (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U)
    (s : Γ(X, U)) :
    (affineInfinitesimalSectionsIso I f n U hU).hom
      (Ideal.Quotient.mk ((I ^ (n + 1)).map (baseOpenSectionsMap f U)) s) =
      (pullback.fst f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)).app U s :=
  QuotientPushout.Construction.quotientPushoutIso_mk _ _ _ _

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.InfinitesimalSections.Construction
