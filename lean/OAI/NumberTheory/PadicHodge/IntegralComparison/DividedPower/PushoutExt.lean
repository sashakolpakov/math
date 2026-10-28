import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PushoutLift

/-! # Pushout Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PushoutExt

noncomputable section

/-!
# IntegralComparison: maps from a divided-power pushout are determined on the two factors
-/

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Pushout OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PushoutLift

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
variable (I : Ideal B) (δ : DividedPowers I) (J : Ideal C) (ε : DividedPowers J)
variable {D : Type u} [CommRing D] {K : Ideal D} {θ : DividedPowers K}

lemma hom_ext (g₁ g₂ : DividedPowers.DPMorphism (Pushout.dividedPowers A B C I δ J ε) θ)
    (hleft : g₁.comp (Pushout.leftMap A B C I δ J ε) = g₂.comp (Pushout.leftMap A B C I δ J ε))
    (hright : g₁.comp (Pushout.rightMap A B C I δ J ε) = g₂.comp (Pushout.rightMap A B C I δ J ε)) : g₁ = g₂ := by
  have h : (g₂.comp (Pushout.leftMap A B C I δ J ε)).toRingHom.comp (algebraMap A B) =
      (g₂.comp (Pushout.rightMap A B C I δ J ε)).toRingHom.comp (algebraMap A C) := by
    change g₂.toRingHom.comp ((Pushout.leftMap A B C I δ J ε).toRingHom.comp (algebraMap A B)) =
      g₂.toRingHom.comp ((Pushout.rightMap A B C I δ J ε).toRingHom.comp (algebraMap A C))
    rw [Pushout.maps_agree]
  exact (PushoutLift.lift_unique A B C I δ J ε (g₂.comp (Pushout.leftMap A B C I δ J ε))
    (g₂.comp (Pushout.rightMap A B C I δ J ε)) h g₁ hleft hright).trans
    (PushoutLift.lift_unique A B C I δ J ε (g₂.comp (Pushout.leftMap A B C I δ J ε))
      (g₂.comp (Pushout.rightMap A B C I δ J ε)) h g₂ rfl rfl).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PushoutExt
