import OAI.NumberTheory.PadicHodge.GeometricComparison.PDTruncationFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.TruncationTransition

/-! # PD Truncation Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PDTruncationLevel.PDTruncationMap

noncomputable section

/-! Functorial divided-power truncation commutes with the original level transitions. -/

universe u v
variable {A : Type u} [CommRing A] {I : Ideal A} {δ : DividedPowers I}
  {B : Type v} [CommRing B] {J : Ideal B} {ε : DividedPowers J}
  (f : DividedPowers.DPMorphism δ ε) (n : ℕ)

theorem level_naturality (m : ℕ) (hnm : n ≤ m) :
    (PDTruncationFunctor.PDTruncationMap.map f n).comp (IntegralComparison.PD.TruncationTransition.map A I n m hnm) =
      (IntegralComparison.PD.TruncationTransition.map B J n m hnm).comp (PDTruncationFunctor.PDTruncationMap.map f m) := by
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PDTruncationLevel.PDTruncationMap
