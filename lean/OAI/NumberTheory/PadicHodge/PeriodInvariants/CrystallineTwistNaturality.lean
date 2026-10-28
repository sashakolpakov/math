import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence

/-! # Crystalline Twist Naturality -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistNaturality

noncomputable section

/-!
# Crystalline base twist commutes with geometric pullback

Twisting the coefficient map and postcomposing the closed-fiber map commute
on the actual thickenings. Their exact sheaf restrictions, including the
inverse coefficient change, have the same compatibility.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist
  CrystallineTwistCohomology

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X Y : Scheme.{u}} {f f' : X ⟶ Spec (CommRingCat.of B)}
  {fY fY' : Y ⟶ Spec (CommRingCat.of B)}
variable (e : B ≃+* B) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (he' : DividedPowers.IsDPMorphism δ δ e.symm.toRingHom)
  (hX : f' = f ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
  (hY : fY' = fY ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
variable (g : X ⟶ Y) (hg : g ≫ fY = f)

include hX hY hg in
theorem twisted_over : g ≫ fY' = f' := by
  rw [hY, ← Category.assoc, hg, hX]

def postcomposeTwist :
    CrystallineBaseTwist.twist (p := p) e he hX ⋙ IntegralComparison.BigCrystallineSite.postcompose g (twisted_over e hX hY g hg) ≅
      IntegralComparison.BigCrystallineSite.postcompose g hg ⋙ CrystallineBaseTwist.twist e he hY := Iso.refl _

def restrictionTwist :
    IntegralComparison.Crystalline.ExactRestriction.restriction (p := p) (J := J) (δ := δ) g (twisted_over e hX hY g hg) ⋙
        CrystallineTwistCohomology.twistedRestriction e he he' hX ≅
      CrystallineTwistCohomology.twistedRestriction e he he' hY ⋙ IntegralComparison.Crystalline.ExactRestriction.restriction g hg := Iso.refl _

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistNaturality
