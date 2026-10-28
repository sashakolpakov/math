import OAI.AlgebraicGeometry.Picard.Homomorphisms.Properties
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Weakly Etale -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WeaklyEtale.WeaklyEtaleFrobenius

noncomputable section

/-! Relative Frobenius is invertible on every weakly étale object of the actual pro-étale site. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem isIso_of_universallyInjective_surjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [WeaklyEtale f] [UniversallyInjective f]
    [Surjective f] [QuasiCompact f] [QuasiSeparated f] : IsIso f := by
  let : Surjective (pullback.diagonal f) :=
    (UniversallyInjective.iff_diagonal f).mp inferInstance
  let : IsIso (pullback.diagonal f) := Flat.isIso_of_surjective_of_mono _
  let : Mono f := (pullback.isIso_diagonal_iff f).mp inferInstance
  exact Flat.isIso_of_surjective_of_mono f

open OAI.AlgebraicGeometry.Picard.Homomorphisms.Properties.Construction

theorem relativeFrobenius_weaklyEtale (p : ℕ) (hp : p.Prime) {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) [WeaklyEtale A.hom] :
    WeaklyEtale (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS A).left := by
  let : WeaklyEtale ((OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS A).left ≫
      (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS A).hom) := by
    rw [Over.w]
    infer_instance
  let : WeaklyEtale (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS A).hom :=
    inferInstanceAs (WeaklyEtale (pullback.snd A.hom (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)))
  exact WeaklyEtale.of_comp _ (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS A).hom

theorem relativeFrobenius_isIso (p : ℕ) (hp : p.Prime) {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) [WeaklyEtale A.hom] :
    IsIso (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS A).left := by
  let := relativeFrobenius_weaklyEtale p hp hS A
  exact isIso_of_universallyInjective_surjective _

theorem absoluteFrobenius_square (p : ℕ) (hp : p.Prime) {X Y : Scheme.{u}}
    (hY : (p : Γ(Y, ⊤)) = 0) (f : X ⟶ Y) [WeaklyEtale f] :
    IsPullback (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.prime_eq_zero_of_map p hY f)) f
      f (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp Y hY) := by
  let A : Over Y := Over.mk f
  let : WeaklyEtale A.hom := inferInstanceAs (WeaklyEtale f)
  let hIso : IsIso (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hY A).left := relativeFrobenius_isIso p hp hY A
  let i := @asIso Scheme _ A.left (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hY A).left
    (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hY A).left hIso
  exact IsPullback.of_iso_pullback
    ⟨OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius_naturality p hp _ hY f⟩ i
    (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius_comp_fst p hp hY A) (OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hY A).w

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WeaklyEtale.WeaklyEtaleFrobenius
