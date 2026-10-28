import OAI.AlgebraicGeometry.Picard.Homomorphisms.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Etale -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Etale.Construction

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits

universe u

variable (p : ℕ) (hp : p.Prime)

set_option backward.isDefEq.respectTransparency.types false in
instance relativeFrobenius_etale {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) [Etale A.hom] :
    Etale (Frobenius.Construction.relativeFrobenius p hp hS A).left := by
  have hcomp : Etale ((Frobenius.Construction.relativeFrobenius p hp hS A).left ≫
      (Frobenius.Construction.frobeniusTwist p hp hS A).hom) := by
    rw [Over.w]
    infer_instance
  have : Etale (Frobenius.Construction.frobeniusTwist p hp hS A).hom :=
    inferInstanceAs (Etale (pullback.snd A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)))
  exact Etale.of_comp _ (Frobenius.Construction.frobeniusTwist p hp hS A).hom

/-- Étale, universally injective, surjective and quasi-compact implies an
isomorphism. The proof first makes the diagonal an isomorphism. -/
theorem isIso_of_etale_universallyInjective_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [UniversallyInjective f]
    [Surjective f] [QuasiCompact f] : IsIso f := by
  have hdiagSurj : Surjective (pullback.diagonal f) :=
    (UniversallyInjective.iff_diagonal f).mp inferInstance
  have hdiagIso : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hdiagSurj⟩
  have : Mono f := (pullback.isIso_diagonal_iff f).mp hdiagIso
  exact Flat.isIso_of_surjective_of_mono f

instance relativeFrobenius_isIso_of_etale {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) [Etale A.hom] :
    IsIso (Frobenius.Construction.relativeFrobenius p hp hS A).left :=
  isIso_of_etale_universallyInjective_surjective _

set_option backward.isDefEq.respectTransparency.types false in
/-- Absolute Frobenius commutes with étale base change. -/
theorem absoluteFrobenius_square_isPullback_of_etale {X Y : Scheme.{u}}
    (hY : (p : Γ(Y, ⊤)) = 0) (f : X ⟶ Y) [Etale f] :
    IsPullback (Frobenius.Construction.absoluteFrobenius p hp X (Frobenius.Construction.prime_eq_zero_of_map p hY f)) f
      f (Frobenius.Construction.absoluteFrobenius p hp Y hY) := by
  let A : Over Y := Over.mk f
  have : Etale A.hom := ‹Etale f›
  have hIso : IsIso (Frobenius.Construction.relativeFrobenius p hp hY A).left :=
    relativeFrobenius_isIso_of_etale p hp hY A
  let i := @asIso Scheme _ A.left (Frobenius.Construction.frobeniusTwist p hp hY A).left
    (Frobenius.Construction.relativeFrobenius p hp hY A).left hIso
  refine IsPullback.of_iso_pullback
    ⟨Frobenius.Construction.absoluteFrobenius_naturality p hp _ hY f⟩
    i ?_ ?_
  · exact Frobenius.Construction.relativeFrobenius_comp_fst p hp hY A
  · exact (Frobenius.Construction.relativeFrobenius p hp hY A).w

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Etale.Construction
