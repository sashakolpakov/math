import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalDetectionOf
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Local Unramified -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalUnramified.LocalUnramifiedCriterion

/-!
# TorsionQuotient: local test rings suffice for formal unramifiedness

Square-zero ideals are transported to the source stalks. The quotient
square commutes by the actual quotient ring homomorphism, and source stalks
jointly detect equality of scheme morphisms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem quotient_precompose {R C : CommRingCat.{u}} (φ : R ⟶ C) (I : Ideal R)
    {X : Scheme.{u}} (a b : Spec R ⟶ X)
    (hab : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ a =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ.hom))) ≫ (Spec.map φ ≫ a) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ.hom))) ≫ (Spec.map φ ≫ b) := by
  let ψ := CommRingCat.ofHom (Ideal.quotientMap (I.map φ.hom) φ.hom Ideal.le_comap_map)
  have hc : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ ψ =
      φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ.hom)) := by
    ext x
    rfl
  have hs : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ.hom))) ≫ Spec.map φ =
      Spec.map ψ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    rw [← Spec.map_comp, ← hc, Spec.map_comp]
  calc
    _ = Spec.map ψ ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ a) := by
      rw [← Category.assoc, hs, Category.assoc]
    _ = Spec.map ψ ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b) :=
      congrArg (fun t => Spec.map ψ ≫ t) hab
    _ = _ := by rw [← Category.assoc, ← hs, Category.assoc]

/-- A square-zero quotient lifting-uniqueness test on local rings implies
the scheme's usual formally-unramified predicate. -/
theorem of_local_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : ∀ (C : CommRingCat.{u}) [IsLocalRing C] (J : Ideal C) (_ : J ^ 2 = ⊥)
      (a b : Spec C ⟶ X),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ b →
      a ≫ f = b ≫ f → a = b) : FormallyUnramified f := by
  apply FormallyUnramified.of_hom_ext
  intro R B φ hφ hI a b hred hp
  let I := RingHom.ker φ.hom
  let ψ := CommRingCat.ofHom (RingHom.quotientKerEquivOfSurjective hφ).symm.toRingHom
  have hφψ : φ ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    ext r
    exact RingHom.quotientKerEquivOfSurjective_symm_apply hφ r
  have hquot : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ a =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b := by
    rw [← hφψ, Spec.map_comp, Category.assoc, Category.assoc, hred]
  apply LocalDetectionOf.LocalDetection.hom_ext_of_fromSpecStalk a b
  intro x
  let ρ := (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial
  have hJ : (I.map ρ.hom) ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, hI, Ideal.map_bot]
  rw [Spec.fromSpecStalk_eq R x]
  exact H ((Spec R).presheaf.stalk x) (I.map ρ.hom) hJ
    (Spec.map ρ ≫ a) (Spec.map ρ ≫ b) (quotient_precompose ρ I a b hquot)
    (by rw [Category.assoc, Category.assoc, hp])

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalUnramified.LocalUnramifiedCriterion
