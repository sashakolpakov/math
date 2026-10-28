import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Transfer

/-! # Ideal PD Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.IdealPDMap

noncomputable section

/-!
# IntegralComparison: maps from a zero divided-power ideal preserve divided powers
-/

universe u v

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B]
  {I : Ideal B} (δ : DividedPowers I) (f : A →+* B)

def map : DividedPowers.DPMorphism (dividedPowersBot A) δ where
  toRingHom := f
  ideal_comp := by simp only [Ideal.map_bot, bot_le]
  dpow_comp x hx := by
    obtain rfl := Ideal.mem_bot.mp hx
    rw [map_zero]
    rename_i n
    by_cases hn : n = 0
    · subst n
      rw [δ.dpow_zero (Ideal.zero_mem _), (dividedPowersBot A).dpow_zero (Ideal.zero_mem _), map_one]
    · rw [δ.dpow_eval_zero hn, (dividedPowersBot A).dpow_eval_zero hn, map_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.IdealPDMap
