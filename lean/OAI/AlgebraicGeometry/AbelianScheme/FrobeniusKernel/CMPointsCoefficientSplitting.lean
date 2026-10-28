import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenLabels
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Integral

/-! # CM Points Coefficient Splitting -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsCoefficientSplitting.Construction

noncomputable section

/-!
The coefficient splittings required by the integral PEL reduction are
derived from the actual CMPoints q-adic coordinates. Their tower and
conjugation compatibilities are proved from those coordinates.
-/

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable (s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))

def l45CoefficientSplitting (n : ℕ) :
    (NumberField.RingOfIntegers E ⧸ Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} :
      Set (NumberField.RingOfIntegers E))) ≃+* ((Fin s × Bool) → ZMod (q ^ n)) :=
  (Ideal.quotEquivOfEq (hsplit n).2.symm).trans
    ((j.residueCoordinates iota n).quotientKerEquivOfSurjective (hsplit n).1) |>.trans
      (RingEquiv.piCongrLeft (fun _ : Gal(E/ℚ) => ZMod (q ^ n)) labels).symm

theorem l45CoefficientSplitting_apply (n : ℕ) (a : NumberField.RingOfIntegers E) (v : Fin s × Bool) :
    l45CoefficientSplitting j iota hsplit s labels n (Ideal.Quotient.mk _ a) v =
      j.residueCharacter iota (labels v) n a := by
  rfl

theorem l45CoefficientSplitting_compatible (n : ℕ) (a : NumberField.RingOfIntegers E) (v : Fin s × Bool) :
    ZMod.castHom (show q ^ n ∣ q ^ (n + 1) by rw [pow_succ]; exact dvd_mul_right _ _) (ZMod (q ^ n))
      (l45CoefficientSplitting j iota hsplit s labels (n + 1) (Ideal.Quotient.mk _ a) v) =
        l45CoefficientSplitting j iota hsplit s labels n (Ideal.Quotient.mk _ a) v :=
  RingHom.congr_fun (j.residueCharacter_compatible iota (labels v) n (n + 1) (Nat.le_succ n)) a

variable [NumberField.IsCMField E]

theorem l45Conjugation_commutes (τ : Gal(E/ℚ)) (x : E) :
    τ (PELModuli.CMPoints.Arithmetic.rationalConjugation E x) = PELModuli.CMPoints.Arithmetic.rationalConjugation E (τ x) := by
  let μ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  apply μ.injective
  exact (NumberField.IsCMField.complexEmbedding_complexConj E (μ.comp τ.toRingHom) x).trans
    (NumberField.IsCMField.complexEmbedding_complexConj E μ (τ x)).symm

theorem l45LocalCharacter_conjugation (τ : Gal(E/ℚ)) (a : NumberField.RingOfIntegers E) :
    j.localCharacter iota τ (NumberField.IsCMField.ringOfIntegersComplexConj E a) =
      j.localCharacter iota (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) a := by
  apply congrArg j.integralEmbedding
  apply NumberField.RingOfIntegers.ext
  exact congrArg iota (l45Conjugation_commutes τ a)

theorem l45CoefficientSplitting_conjugation
    (hlabels : ∀ (v : Fin s) (b : Bool), labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))
    (n : ℕ) (a : NumberField.RingOfIntegers E) (v : Fin s) (b : Bool) :
    l45CoefficientSplitting j iota hsplit s labels n
        (Ideal.Quotient.mk _ (NumberField.IsCMField.ringOfIntegersComplexConj E a)) (v, b) =
      l45CoefficientSplitting j iota hsplit s labels n (Ideal.Quotient.mk _ a) (v, !b) := by
  rw [l45CoefficientSplitting_apply, l45CoefficientSplitting_apply, hlabels]
  exact congrArg (PadicInt.toZModPow n) (l45LocalCharacter_conjugation j iota (labels (v, b)) a)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsCoefficientSplitting.Construction
