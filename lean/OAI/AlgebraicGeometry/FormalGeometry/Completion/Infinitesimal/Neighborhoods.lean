import OAI.AlgebraicGeometry.FormalGeometry.Completion.QuotientPower
import Mathlib.AlgebraicGeometry.Limits

/-! # Neighborhoods -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.Neighborhoods.Construction

noncomputable section

/-! # Completion: actual infinitesimal neighborhoods and their closed homeomorphisms -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The positive infinitesimal base cut out by the indicated ideal power. -/
def infinitesimalBase (n : ℕ) : Scheme.{u} := Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))

def infinitesimalBaseToSpec (n : ℕ) : infinitesimalBase I n ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))

def infinitesimalBaseTransition (n : ℕ) : infinitesimalBase I n ⟶ infinitesimalBase I (n + 1) :=
  QuotientPower.Construction.quotientPowerMap I (Nat.le_succ (n + 1))

instance infinitesimalBaseTransition_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (infinitesimalBaseTransition I n) := by
  unfold infinitesimalBaseTransition
  infer_instance

instance infinitesimalBaseTransition_surjective (n : ℕ) :
    Surjective (infinitesimalBaseTransition I n) :=
  QuotientPower.Construction.quotientPowerMap_surjective I (Nat.zero_lt_succ n) (Nat.le_succ (n + 1))

@[reassoc]
theorem infinitesimalBaseTransition_toSpec (n : ℕ) :
    infinitesimalBaseTransition I n ≫ infinitesimalBaseToSpec I (n + 1) =
      infinitesimalBaseToSpec I n := by
  dsimp [infinitesimalBaseTransition, infinitesimalBaseToSpec, QuotientPower.Construction.quotientPowerMap]
  rw [← Spec.map_comp]
  congr 1

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The actual base change of the family to a positive infinitesimal base. -/
def infinitesimalNeighborhood (n : ℕ) : Scheme.{u} := pullback f (infinitesimalBaseToSpec I n)

/-- The actual inclusion into the next infinitesimal neighborhood. -/
def infinitesimalTransition (n : ℕ) :
    infinitesimalNeighborhood I f n ⟶ infinitesimalNeighborhood I f (n + 1) :=
  pullback.map _ _ _ _ (𝟙 _) (infinitesimalBaseTransition I n) (𝟙 _)
    (by simp) (by simp [infinitesimalBaseTransition_toSpec])

theorem infinitesimalTransition_isPullback (n : ℕ) :
    IsPullback (infinitesimalTransition I f n) (pullback.snd f (infinitesimalBaseToSpec I n))
      (pullback.snd f (infinitesimalBaseToSpec I (n + 1))) (infinitesimalBaseTransition I n) := by
  refine .of_right (t := IsPullback.of_hasPullback f (infinitesimalBaseToSpec I (n + 1))) ?_ ?_
  · simpa [infinitesimalTransition, infinitesimalBaseTransition_toSpec] using
      (IsPullback.of_hasPullback f (infinitesimalBaseToSpec I n))
  · dsimp [infinitesimalTransition]
    cat_disch

instance infinitesimalTransition_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (infinitesimalTransition I f n) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (infinitesimalTransition_isPullback I f n).flip inferInstance

instance infinitesimalTransition_surjective (n : ℕ) :
    Surjective (infinitesimalTransition I f n) :=
  MorphismProperty.of_isPullback (P := @Surjective)
    (infinitesimalTransition_isPullback I f n).flip inferInstance

/-- Infinitesimal neighborhood inclusions are homeomorphisms on the actual underlying spaces. -/
def infinitesimalTransitionHomeomorph (n : ℕ) :
    infinitesimalNeighborhood I f n ≃ₜ infinitesimalNeighborhood I f (n + 1) :=
  (infinitesimalTransition I f n).isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
    (infinitesimalTransition I f n).surjective

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.Neighborhoods.Construction
