import OAI.NumberTheory.PadicHodge.GeometricComparison.PDTruncationFunctor

/-! # PD Truncation Core -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PDTruncationCore.PDTruncationSquare

noncomputable section

/-! A commuting square of divided-power maps remains commutative
after the original prime-power truncations. -/

variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  {IA : Ideal A} {IB : Ideal B} {IC : Ideal C} {ID : Ideal D}
  {δA : DividedPowers IA} {δB : DividedPowers IB} {δC : DividedPowers IC} {δD : DividedPowers ID}
  (a : DividedPowers.DPMorphism δB δA) (b : DividedPowers.DPMorphism δC δA)
  (c : DividedPowers.DPMorphism δD δB) (d : DividedPowers.DPMorphism δD δC)
  (n : ℕ) (h : ∀ x, a (c x) = b (d x))

include h in
theorem square : (PDTruncationFunctor.PDTruncationMap.map a n).comp (PDTruncationFunctor.PDTruncationMap.map c n) =
    (PDTruncationFunctor.PDTruncationMap.map b n).comp (PDTruncationFunctor.PDTruncationMap.map d n) := by
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (Ideal.Quotient.mk (IA ^ (n + 1))) (h y)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PDTruncationCore.PDTruncationSquare
