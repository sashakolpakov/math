import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Moduli
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ReferenceFrame
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteCoordinates
import OAI.AlgebraicGeometry.PELModuli.CMPoints.SplitCoordinates
import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic

/-! # Prime Bounds -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrimeBounds.Intrinsic

noncomputable section

/-! All bounds needed by the retained test and the chosen integral model
are fixed before the prime. The split-coordinate bound applies to every
later q-adic choice, including the one required by comparison. -/

open scoped Classical _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ReferenceFrame.ParameterChoices

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
  (M : Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)

def retainedSplitCoordinateBound : ℕ := (PELModuli.CMPoints.SplitCoordinates.exists_split_coordinates_bound E).choose

def retainedQadicChoiceBound : ℕ :=
  (PELModuli.CMPoints.LocalPadic.exists_qadicChoice_bound M.integral.base.embedding).choose

def retainedPrimeBounds : Finset ℕ :=
  {2, R.thetaTest.level,
    Intrinsic.FiniteCoordinates.nativeCoordinateBound E P hP v R.coordinates R.pairing,
    Intrinsic.ReferenceFrame.ParameterChoices.referenceFrameBound E P hP, M.level, M.integral.base.denominator,
    ∏ i, P.polarizationType i, retainedSplitCoordinateBound E,
    retainedQadicChoiceBound E P hP hμ v hv W R M}

def retainedPrimeBound : ℕ := (retainedPrimeBounds E P hP hμ v hv W R M).sup id

structure RetainedPrimeConditions (q : ℕ) [Fact q.Prime] : Prop where
  test_large : max 2 (max R.thetaTest.level
    (Intrinsic.FiniteCoordinates.nativeCoordinateBound E P hP v R.coordinates R.pairing)) < q
  frame_large : Intrinsic.ReferenceFrame.ParameterChoices.referenceFrameBound E P hP < q
  level_coprime : q.Coprime M.level
  denominator_coprime : q.Coprime M.integral.base.denominator
  polarization_coprime : q.Coprime (∏ i, P.polarizationType i)
  split_coordinates : ∀ (K : Type) [Field K] [NumberField K]
    (κ : K →+* ℂ) (iota : E →+* K) (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q),
    j.HasSplitCoordinates iota
  qadic_choice : PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt M.integral.base.extension.carrier q →
    Nonempty (PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)

theorem retained_prime_conditions {q : ℕ} [Fact q.Prime]
    (hq : retainedPrimeBound E P hP hμ v hv W R M < q) :
    RetainedPrimeConditions E P hP hμ v hv W R M q := by
  have hb : ∀ n ∈ retainedPrimeBounds E P hP hμ v hv W R M, n < q := by
    intro n hn
    exact lt_of_le_of_lt (Finset.le_sup (f := id) hn) hq
  have htwo : 2 < q := hb _ (by simp [retainedPrimeBounds])
  have htest : R.thetaTest.level < q := hb _ (by simp [retainedPrimeBounds])
  have hcoord : Intrinsic.FiniteCoordinates.nativeCoordinateBound E P hP v R.coordinates R.pairing < q :=
    hb _ (by simp [retainedPrimeBounds])
  have hframe : Intrinsic.ReferenceFrame.ParameterChoices.referenceFrameBound E P hP < q := hb _ (by simp [retainedPrimeBounds])
  have hlevel : M.level < q := hb _ (by simp [retainedPrimeBounds])
  have hden : M.integral.base.denominator < q := hb _ (by simp [retainedPrimeBounds])
  have hpol : (∏ i, P.polarizationType i) < q := hb _ (by simp [retainedPrimeBounds])
  have hsplit : retainedSplitCoordinateBound E < q := hb _ (by simp [retainedPrimeBounds])
  have hchoice : retainedQadicChoiceBound E P hP hμ v hv W R M < q :=
    hb _ (by simp [retainedPrimeBounds])
  have hpolpos : 0 < ∏ i, P.polarizationType i := by
    apply Finset.prod_pos
    intro i _
    exact hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i
  refine ⟨max_lt htwo (max_lt htest hcoord), hframe, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.coprime_of_lt_prime
      (lt_of_lt_of_le (by decide : 0 < 3) M.level_ge_three).ne' hlevel (Fact.out : q.Prime)
  · exact Nat.coprime_of_lt_prime M.integral.base.denominator_ne_zero hden (Fact.out : q.Prime)
  · exact Nat.coprime_of_lt_prime hpolpos.ne' hpol (Fact.out : q.Prime)
  · intro K _ _ κ iota j
    exact (PELModuli.CMPoints.SplitCoordinates.exists_split_coordinates_bound E).choose_spec K κ iota q j hsplit
  · exact (PELModuli.CMPoints.LocalPadic.exists_qadicChoice_bound M.integral.base.embedding).choose_spec q hchoice

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrimeBounds.Intrinsic
