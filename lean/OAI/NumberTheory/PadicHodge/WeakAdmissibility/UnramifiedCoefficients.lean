import OAI.NumberTheory.PadicHodge.WeakAdmissibility.TiltCoefficients
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonScalars

/-! # Unramified Coefficients -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients

noncomputable section

/-! Actual Witt coefficient fields in B_cris, with their periodic Frobenius. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements OAI.NumberTheory.PadicHodge.WeakAdmissibility.TiltCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois.PeriodStructure
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonBd
variable (p : ℕ) [Fact p.Prime]
variable {k : Type*} [Field k] [Fintype k] [CharP k p] (j : k →+* PrimitiveElements.ResidueCp p)

abbrev CoefficientField := FractionRing (WittVector p k)

def coefficientToAInf : WittVector p k →+* Logarithm.PeriodRings.AInf p := WittVector.map (TiltCoefficients.coefficientEmbedding p j)

theorem coefficientToAInf_injective : Function.Injective (coefficientToAInf p j) :=
  WittVector.map_injective _ (TiltCoefficients.coefficientEmbedding p j).injective

def coefficientToUncompleted : WittVector p k →+* Logarithm.PeriodRings.ACrisUncompleted p :=
  (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p)).comp (coefficientToAInf p j)

def coefficientToACris : WittVector p k →+* Logarithm.PeriodRings.ACris p :=
  (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p)).comp (coefficientToUncompleted p j)

def coefficientToPositive : WittVector p k →+* Logarithm.PeriodRings.BCrisPlus p :=
  (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p)).comp (coefficientToACris p j)

def coefficientToBCris : WittVector p k →+* Logarithm.PeriodRings.BCris p :=
  (algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p)).comp (coefficientToPositive p j)

theorem coefficient_nonzero_isUnit (x : WittVector p k) (hx : x ≠ 0) : IsUnit (coefficientToBCris p j x) := by
  obtain ⟨n, u, hu⟩ := WittVector.exists_eq_pow_p_mul' x hx
  rw [hu, map_mul, map_pow, map_natCast]
  apply IsUnit.mul
  · apply IsUnit.pow
    simpa only [map_natCast] using
      (IsLocalization.Away.algebraMap_isUnit (p : Logarithm.PeriodRings.ACris p)).map (algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p))
  · exact u.isUnit.map (coefficientToBCris p j)

/-- The finite unramified Witt coefficient field, embedded into the actual crystalline ring. -/
def coefficientFieldToBCris : CoefficientField (p := p) (k := k) →+* Logarithm.PeriodRings.BCris p :=
  IsLocalization.lift (g := coefficientToBCris p j)
    (fun x : nonZeroDivisors (WittVector p k) => coefficient_nonzero_isUnit p j x
      (mem_nonZeroDivisors_iff_ne_zero.mp x.property))

theorem coefficientFieldToBCris_integer (x : WittVector p k) :
    coefficientFieldToBCris p j (algebraMap (WittVector p k) (CoefficientField (p := p) (k := k)) x) =
      coefficientToBCris p j x := by
  unfold coefficientFieldToBCris
  rw [IsLocalization.lift_eq]

theorem coefficientFieldToBCris_injective : Function.Injective (coefficientFieldToBCris p j) :=
  (coefficientFieldToBCris p j).injective

theorem coefficientToAInf_frobenius (x : WittVector p k) :
    Logarithm.PeriodRings.aInfFrobenius p (coefficientToAInf p j x) = coefficientToAInf p j (WittVector.frobenius x) := by
  change WittVector.frobenius (WittVector.map (TiltCoefficients.coefficientEmbedding p j) x) =
    WittVector.map (TiltCoefficients.coefficientEmbedding p j) (WittVector.frobenius x)
  ext n
  simp only [WittVector.coeff_frobenius_charP, WittVector.map_coeff, map_pow]

theorem coefficientToUncompleted_frobenius (x : WittVector p k) :
    Logarithm.PeriodRings.aCrisUncompletedFrobenius p (coefficientToUncompleted p j x) =
      coefficientToUncompleted p j (WittVector.frobenius x) :=
  (Galois.PeriodStructure.uncompletedFrobenius_algebraMap p (coefficientToAInf p j x)).trans
    (congrArg (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p)) (coefficientToAInf_frobenius p j x))

theorem coefficientToACris_frobenius (x : WittVector p k) :
    Logarithm.PeriodRings.aCrisFrobenius p (coefficientToACris p j x) = coefficientToACris p j (WittVector.frobenius x) :=
  (Galois.PeriodStructure.aCrisFrobenius_algebraMap p (coefficientToUncompleted p j x)).trans
    (congrArg (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p)) (coefficientToUncompleted_frobenius p j x))

theorem coefficientToPositive_frobenius (x : WittVector p k) :
    Logarithm.PeriodRings.bCrisPlusFrobenius p (coefficientToPositive p j x) =
      coefficientToPositive p j (WittVector.frobenius x) :=
  (Logarithm.PeriodRings.bCrisPlusFrobenius_algebraMap p (coefficientToACris p j x)).trans
    (congrArg (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p)) (coefficientToACris_frobenius p j x))

theorem coefficientToBCris_frobenius (x : WittVector p k) :
    Logarithm.bCrisFrobenius p (coefficientToBCris p j x) = coefficientToBCris p j (WittVector.frobenius x) :=
  (Logarithm.bCrisFrobenius_algebraMap p (coefficientToPositive p j x)).trans
    (congrArg (algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p)) (coefficientToPositive_frobenius p j x))

def coefficientFrobenius : CoefficientField (p := p) (k := k) ≃+* CoefficientField (p := p) (k := k) :=
  IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p k)

theorem coefficientFrobenius_integer (x : WittVector p k) :
    coefficientFrobenius (p := p) (k := k)
      (algebraMap (WittVector p k) (CoefficientField (p := p) (k := k)) x) =
      algebraMap (WittVector p k) (CoefficientField (p := p) (k := k)) (WittVector.frobenius x) := by
  unfold coefficientFrobenius
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

theorem coefficientFieldToBCris_frobenius (x : CoefficientField (p := p) (k := k)) :
    Logarithm.bCrisFrobenius p (coefficientFieldToBCris p j x) =
      coefficientFieldToBCris p j (coefficientFrobenius (p := p) (k := k) x) := by
  have he : (Logarithm.bCrisFrobenius p).comp (coefficientFieldToBCris p j) =
      (coefficientFieldToBCris p j).comp (coefficientFrobenius (p := p) (k := k)).toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, coefficientFieldToBCris_integer,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coefficientFrobenius_integer]
    exact coefficientToBCris_frobenius p j a
  exact DFunLike.congr_fun he x

def residueDegree : ℕ+ := (FiniteField.card k p).choose

omit [Fact p.Prime] in
theorem residueDegree_card : Fintype.card k = p ^ (residueDegree (p := p) (k := k) : ℕ) :=
  (FiniteField.card k p).choose_spec.2

theorem wittFrobenius_period (x : WittVector p k) :
    (WittVector.frobenius : WittVector p k → WittVector p k)^[residueDegree (p := p) (k := k)] x = x := by
  ext n
  rw [WittVector.iterate_frobenius_coeff, ← residueDegree_card, FiniteField.pow_card]

theorem coefficientFrobenius_iterate_integer (n : ℕ) (x : WittVector p k) :
    (coefficientFrobenius (p := p) (k := k))^[n]
      (algebraMap (WittVector p k) (CoefficientField (p := p) (k := k)) x) =
      algebraMap (WittVector p k) (CoefficientField (p := p) (k := k))
        ((WittVector.frobenius : WittVector p k → WittVector p k)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, coefficientFrobenius_integer]

theorem coefficientFrobenius_period (x : CoefficientField (p := p) (k := k)) :
    (coefficientFrobenius (p := p) (k := k))^[residueDegree (p := p) (k := k)] x = x := by
  have hdiv (n : ℕ) (a b : CoefficientField (p := p) (k := k)) :
      (coefficientFrobenius (p := p) (k := k))^[n] (a / b) =
        (coefficientFrobenius (p := p) (k := k))^[n] a /
          (coefficientFrobenius (p := p) (k := k))^[n] b := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, map_div₀]
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := WittVector p k) x
  rw [hdiv, coefficientFrobenius_iterate_integer, coefficientFrobenius_iterate_integer,
    wittFrobenius_period, wittFrobenius_period]

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients
