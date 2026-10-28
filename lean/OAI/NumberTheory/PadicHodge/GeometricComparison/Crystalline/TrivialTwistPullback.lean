import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TwistCohomologyIdentity

/-! # Trivial Twist Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TrivialTwistPullback.CrystallineTwistIdentity

noncomputable section

/-! An identity coefficient twist returns the actual scheme pullback to its original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

theorem trivial_twist_after_pullback
    {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
    {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
    (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (e : B ≃+* B) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
    (he' : DividedPowers.IsDPMorphism δ δ e.symm.toRingHom) (heq : e = RingEquiv.refl B)
    (h : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
    (n : ℕ) (x : IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fY n) :
    PeriodInvariants.CrystallineTwistCohomology.cohomologyMap e he he' h n (IntegralComparison.BigCrystallineCohomology.pullback g rfl n x) =
      IntegralComparison.BigCrystallineCohomology.pullback g hg n x := by
  subst e
  subst fX
  exact TwistCohomologyIdentity.CrystallineTwistIdentity.cohomologyMap_refl (g ≫ fY) he n (IntegralComparison.BigCrystallineCohomology.pullback g rfl n x)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TrivialTwistPullback.CrystallineTwistIdentity
