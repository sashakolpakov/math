import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.FrobeniusGeometry

/-! # Prime Zero -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PrimeZero.PrimeZeroSpecFrobenius

noncomputable section

/-! The p-power map of a ring killed by p induces the actual absolute
scheme Frobenius, naturally under maps from its spectrum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] (hp : (p : A) = 0)

include hp in
omit [Fact p.Prime] in
theorem sections_prime_zero : (p : Γ(Spec (CommRingCat.of A), ⊤)) = 0 := by
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv hp
  simpa only [map_natCast, map_zero] using h

theorem scheme : AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p Fact.out (Spec (CommRingCat.of A))
    (sections_prime_zero p A hp) =
      Spec.map (CommRingCat.ofHom (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p Fact.out A hp)) := by
  apply IntegralComparison.Global.FrobeniusGeometry.hom_ext_appTop
  apply (CategoryTheory.cancel_mono (Scheme.ΓSpecIso (CommRingCat.of A)).hom).mp
  rw [Scheme.ΓSpecIso_naturality]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (s ^ p) =
    ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom s) ^ p
  exact map_pow _ s p

theorem naturality {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0)
    (f : Spec (CommRingCat.of A) ⟶ X) :
    Spec.map (CommRingCat.ofHom (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p Fact.out A hp)) ≫ f =
      f ≫ AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p Fact.out X hX := by
  rw [← scheme p A hp]
  exact AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius_naturality p Fact.out (sections_prime_zero p A hp) hX f

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PrimeZero.PrimeZeroSpecFrobenius
