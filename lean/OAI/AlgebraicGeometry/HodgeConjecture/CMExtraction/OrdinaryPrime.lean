import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryModel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrimeBounds
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedClosureOrdinaryDensity

/-! # Ordinary Prime -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryPrime.Intrinsic

noncomputable section

/-! A common prime for the retained theta test, integral model, and
full dense ordinary reduction. The comparison closures remain free to
be selected afterwards, so the native opposite place uses this same q. -/

open scoped Classical _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedClosureOrdinaryDensity.Ordinary

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem exists_retained_dense_ordinary_prime
    (hOpenness : PELModuli.CMPoints.OrdinaryReduction.OpennessInput) (hSplitPrimes : PELModuli.CMPoints.Arithmetic.SplitPrimesInput)
    (hHilb : PELModuli.IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : PELModuli.IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hCMAbelianVarietyA : PELModuli.CMPoints.Descent.AbelianInput) (hCMAbelianVarietyM : PELModuli.CMPoints.Descent.ModuliInput)
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {s : ℕ} (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
    (R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
    (M : Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)
    (excluded : Finset ℕ) (bound : ℕ) :
    let Q := OrdinaryModel.Intrinsic.retainedOrdinaryModel E P hP hμ v hv W R M
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt E q ∧
      PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt M.integral.base.extension.carrier q ∧
      PrimeBounds.Intrinsic.RetainedPrimeConditions E P hP hμ v hv W R M q ∧
      ∀ (jC : ParameterChoices.Qbar →+* ℂ) (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q]),
      ∃ j : Q.QadicChoice q,
        j.complexClosure = jC ∧ j.iota = ι ∧
        j.fieldInClosure = (CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure jC Q.arithmetic.embedding).toRingHom ∧
        j.HasSplitCoordinates Q.extendedEmbedding ∧
        ∃ T : Q.GoodIntegralReduction q j,
          (∀ a : Q.Family, IsOpen (T.ordinaryLocus a) ∧
            ∀ x : T.geom a, Dense {y : connectedComponent x | T.IsOrdinary a y.val}) ∧
          ∃ chosen : Set Gal(E/ℚ),
            let c := (NumberField.IsCMField.complexConj E).restrictScalars ℚ
            c ∈ chosen ∧ (∀ τ, τ ∈ chosen ↔ c * τ ∉ chosen) ∧
            (∀ (a : Q.Family) (x : T.geom a) (τ : Gal(E/ℚ)),
              T.HasHeight a x τ 3 ∧ T.PolarizationDuality a x τ (c * τ)) ∧
            (∀ (a : Q.Family) (x : T.geom a),
              T.HasLieRank a x c 1 ∧
              ∀ τ ∈ chosen, τ ≠ c → T.HasLieRank a x τ 0 ∨ T.HasLieRank a x τ 3) := by
  let Q := OrdinaryModel.Intrinsic.retainedOrdinaryModel E P hP hμ v hv W R M
  have hQ := OrdinaryModel.Intrinsic.retainedOrdinaryModel_periods E P hP hμ v hv W R M hs hdegree
  obtain ⟨q, hq, hb, hx, hE, _, hK, _, hchoices⟩ :=
    FixedClosureOrdinaryDensity.Ordinary.exists_fixed_closure_dense_ordinary hOpenness hSplitPrimes hHilb hEnd hCMAbelianVarietyA hCMAbelianVarietyM
      E E Q hQ (fun _ : Unit => E) excluded
      (max bound (PrimeBounds.Intrinsic.retainedPrimeBound E P hP hμ v hv W R M))
  let : Fact q.Prime := ⟨hq⟩
  exact ⟨q, hq, lt_of_le_of_lt (le_max_left _ _) hb, hx, hE, hK,
    PrimeBounds.Intrinsic.retained_prime_conditions E P hP hμ v hv W R M
      (lt_of_le_of_lt (le_max_right _ _) hb), hchoices⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryPrime.Intrinsic
