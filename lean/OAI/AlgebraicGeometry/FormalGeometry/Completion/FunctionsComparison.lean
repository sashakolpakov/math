import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ClopenSections
import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Functions Comparison -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FunctionsComparison.Construction

noncomputable section

/-!
# Completion: the actual comparison from the completed base to infinitesimal global sections

This constructs the canonical comparison using the actual quotient-ring
maps, structure morphisms, and compatible-section ring. It does not assert
surjectivity or the formal-functions theorem.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Actual evaluations from the adic completion commute with the quotient transitions. -/
theorem adicCompletion_factor_eval {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  have hs := AdicCompletion.AdicCauchySequence.mk_eq_mk h s
  change Ideal.Quotient.mk (I ^ m • ⊤) (s n) = Ideal.Quotient.mk (I ^ m • ⊤) (s m) at hs
  have hI : (I ^ m • ⊤ : Ideal R) = I ^ m := by ext r; simp
  rw [hI] at hs
  exact hs

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The actual structure map on global functions at each infinitesimal level. -/
def infinitesimalBaseSectionsMap (n : ℕ) : R ⧸ I ^ (n + 1) →+*
    Γ(Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood I f n, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (n + 1)))).inv ≫
    (pullback.snd f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)).appTop).hom

theorem infinitesimalBaseSectionsMap_compatible (n : ℕ) :
    (Infinitesimal.Neighborhoods.Construction.infinitesimalTransition I f n).appTop.hom.comp (infinitesimalBaseSectionsMap I f (n + 1)) =
      (infinitesimalBaseSectionsMap I f n).comp (Ideal.Quotient.factorPowSucc I (n + 1)) := by
  have he : Infinitesimal.Neighborhoods.Construction.infinitesimalTransition I f n ≫
      pullback.snd f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I (n + 1)) =
      pullback.snd f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ Infinitesimal.Neighborhoods.Construction.infinitesimalBaseTransition I n := by
    simp [Infinitesimal.Neighborhoods.Construction.infinitesimalTransition]
  change (((Scheme.ΓSpecIso _).inv ≫
    (pullback.snd f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I (n + 1))).appTop) ≫
      (Infinitesimal.Neighborhoods.Construction.infinitesimalTransition I f n).appTop).hom =
    (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1)) ≫
      (Scheme.ΓSpecIso _).inv ≫ (pullback.snd f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)).appTop).hom
  congr 1
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, he, Scheme.Hom.comp_appTop, ← Category.assoc]
  exact congrArg (fun k => k ≫ (pullback.snd f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)).appTop)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (Ideal.Quotient.factorPowSucc I (n + 1)))).symm

/-- The canonical ring homomorphism from the completed base to actual compatible global sections. -/
def formalFunctionsComparison : AdicCompletion I R →+* Infinitesimal.ClopenSections.Construction.infinitesimalGlobalSections I f where
  toFun x := ⟨fun n => infinitesimalBaseSectionsMap I f n (AdicCompletion.evalₐ I (n + 1) x), by
    intro n
    change ((Infinitesimal.Neighborhoods.Construction.infinitesimalTransition I f n).appTop.hom.comp
      (infinitesimalBaseSectionsMap I f (n + 1))) (AdicCompletion.evalₐ I (n + 1 + 1) x) = _
    rw [infinitesimalBaseSectionsMap_compatible]
    change infinitesimalBaseSectionsMap I f n
      (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
        (AdicCompletion.evalₐ I (n + 1 + 1) x)) = _
    rw [adicCompletion_factor_eval]⟩
  map_zero' := by apply Subtype.ext; funext n; simp
  map_one' := by apply Subtype.ext; funext n; simp
  map_add' x y := by apply Subtype.ext; funext n; simp
  map_mul' x y := by apply Subtype.ext; funext n; simp

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FunctionsComparison.Construction
