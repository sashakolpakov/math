import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientLiftArray
import OAI.Algorithms.SubexponentialSAT.SubexpExplicitLift
import OAI.Algorithms.SubexponentialSAT.SubexpSelectedConversions
import OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm

namespace OAI.Algorithms

/-! Complete coefficient-array lifting agrees with the exact polynomial
section used by the layout. No homomorphism property of the section is used. -/

namespace SubexponentialSAT.SubexpRowLiftSemantics

open SubexpLiftRing SubexpQuarticRing

private theorem coeff_map_inside {C E L : Type*} [Semiring E] [Semiring L]
    (source : C → E) (target : C → L) (sectionValue : E → L)
    (h : ∀ a, target a = sectionValue (source a))
    (P : List C) (i : ℕ) (hi : i < P.length) :
    PolynomialAlgorithm.coeff (P.map target) i =
      sectionValue (PolynomialAlgorithm.coeff (P.map source) i) := by
  induction P generalizing i with
  | nil => simp at hi
  | cons a P ih =>
      cases i with
      | zero => exact h a
      | succ i =>
          exact ih i (by simpa using hi)

theorem coefficientwise_lift {C A E L : Type*} [CommSemiring E] [CommSemiring L]
    (source : C → E) (target : A → L) (lift : C → A) (sectionValue : E → L)
    (h : ∀ a, target (lift a) = sectionValue (source a))
    (R : ℕ) (P : List C) (hlen : P.length = R + 1) :
    PolynomialAlgorithm.denote ((P.map lift).map target) =
      SubexpExplicitLift.liftPolynomial sectionValue R (PolynomialAlgorithm.denote (P.map source)) := by
  ext i
  rw [PolynomialAlgorithm.coeff_denote, SubexpExplicitLift.coeff_liftPolynomial,
    PolynomialAlgorithm.coeff_denote]
  simp only [List.map_map]
  by_cases hi : i ≤ R
  · rw [ite_eq_left hi]
    exact coeff_map_inside source (target ∘ lift) sectionValue h P i (by omega)
  · rw [ite_eq_right hi]
    exact PolynomialAlgorithm.coeff_eq_zero_of_length_le _ i (by simp [hlen]; omega)

variable (p μ : ℕ) [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0)

noncomputable def targetDecode (a : Quad (Word (baseWidth p μ))) : SubexpActualRing.Ring p μ :=
  quotientDenote (QuarticSearch.liftedCoefficients p μ) (a.map (wordValue p μ))

/-- This is the exact list computed by the concrete array-lift loop. -/
theorem liftedArray_denote (hμ : 0 < μ) (R : ℕ)
    (P : List (Quad (Word (baseWidth p 1)))) (hlen : P.length = R + 1) :
    PolynomialAlgorithm.denote
        ((SubexpCoefficientLiftArray.liftedArray p μ source.modulus P).map (targetDecode p μ)) =
      SubexpExplicitLift.liftPolynomial (SubexpActualRing.sectionValue p μ hμ) R
        (PolynomialAlgorithm.denote (P.map source.residueRing.decode)) := by
  apply coefficientwise_lift source.residueRing.decode (targetDecode p μ)
    (fun a => (SubexpWordLift.liftQuadRun p μ source.modulus a).1)
    (SubexpActualRing.sectionValue p μ hμ) _ R P hlen
  intro a
  rw [SubexpSelectedConversions.Prepared.residueRing_decode]
  exact SubexpWordLift.liftQuadRun_section p μ source.modulus hμ a

end SubexponentialSAT.SubexpRowLiftSemantics

end OAI.Algorithms
