import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter
import Mathlib.RingTheory.WittVector.Frobenius

/-! # Witt Frobenius -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WittFrobenius.Crystalline

noncomputable section

/-! At the split prime, the actual Witt and fraction-field coefficient Frobenius are identities. -/

variable (q : ℕ) [Fact q.Prime]

theorem wittFrobenius_eq_id :
    WittVector.frobeniusEquiv q (ZMod q) = RingEquiv.refl (Crystalline.CoefficientAdapter.Witt q) := by
  apply RingEquiv.ext
  intro w
  apply WittVector.ext
  intro n
  change (WittVector.frobenius w).coeff n = w.coeff n
  rw [WittVector.coeff_frobenius_charP]
  simp

theorem fractionFrobenius_eq_id :
    (IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv q (ZMod q)) :
      FractionRing (Crystalline.CoefficientAdapter.Witt q) ≃+* FractionRing (Crystalline.CoefficientAdapter.Witt q)) = RingEquiv.refl _ := by
  rw [wittFrobenius_eq_id, IsFractionRing.ringEquivOfRingEquiv_refl]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WittFrobenius.Crystalline
