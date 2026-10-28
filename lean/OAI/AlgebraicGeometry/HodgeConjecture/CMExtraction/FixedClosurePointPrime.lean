import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CompatiblePrime

/-! # Fixed Closure Point Prime -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedClosurePointPrime.ParameterChoices

noncomputable section

/-! One prime works for the actual point fields and every subsequently
chosen algebraic-closure embedding. The same q-adic choice supplies their
compatible embeddings, split coordinates and good integral reduction. -/

open OAI.AlgebraicGeometry.PELModuli.CMPoints.CompatiblePrime

theorem exists_fixed_closure_point_field_prime
    (hSplitPrimes : PELModuli.CMPoints.Arithmetic.SplitPrimesInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    {PointIdx : Type} [Finite PointIdx] (F : PointIdx → Type)
    [∀ u, Field (F u)] [∀ u, NumberField (F u)]
    (iF : ∀ u, M.arithmetic.extension.carrier →+* F u)
    {Idx : Type} [Finite Idx] (L : Idx → Type)
    [∀ u, Field (L u)] [∀ u, NumberField (L u)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt E q ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt K q ∧
      PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧
      (∀ u, PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt (L u) q) ∧ (∀ u, PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt (F u) q) ∧
      ∀ (jC : ParameterChoices.Qbar →+* ℂ) (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q]),
      ∃ (j : M.QadicChoice q) (fF : ∀ u, F u →+* ℚ_[q]),
        j.complexClosure = jC ∧ j.iota = ι ∧
        j.fieldInClosure = (CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure jC M.arithmetic.embedding).toRingHom ∧
        (∀ u, (fF u).comp (iF u) = j.completion.toRingHom.comp
          (NumberField.FinitePlace.embedding j.prime)) ∧
        j.HasSplitCoordinates M.extendedEmbedding ∧ Nonempty (M.GoodIntegralReduction q j) := by
  obtain ⟨C, hC, iB, eF, _, hc⟩ := PELModuli.CMPoints.CommonEmbeddedFields.exists_compatible_common_field M.arithmetic.embedding F iF
  let : NumberField C := hC
  let N := ComplexMultiplication.CommonCMField.CM.conjugateCompositum (fun _ : Unit => C)
  let iC : C →+* N :=
    (ComplexMultiplication.CommonCMField.CM.conjugateCompositum.embedding (fun _ : Unit => C) () (IsAlgClosed.lift : C →ₐ[ℚ] ℂ)).toRingHom
  let iN := iC.comp iB
  let V := ComplexMultiplication.CommonCMField.CM.conjugateCompositum L
  let fields : Bool × Bool → Type
    | (false, false) => E
    | (false, true) => K
    | (true, false) => N
    | (true, true) => V
  let fieldStructures : ∀ u, Field (fields u)
    | (false, false) => inferInstanceAs (Field E)
    | (false, true) => inferInstanceAs (Field K)
    | (true, false) => inferInstanceAs (Field N)
    | (true, true) => inferInstanceAs (Field V)
  let numberFields : ∀ u, NumberField (fields u)
    | (false, false) => inferInstanceAs (NumberField E)
    | (false, true) => inferInstanceAs (NumberField K)
    | (true, false) => inferInstanceAs (NumberField N)
    | (true, true) => inferInstanceAs (NumberField V)
  obtain ⟨dN, hdN⟩ := PELModuli.CMPoints.LocalPadic.exists_padic_embedding_bound N
  obtain ⟨dE, hdE⟩ := PELModuli.CMPoints.SplitCoordinates.exists_split_coordinates_bound E
  obtain ⟨q, hq, hb, hx, hs⟩ := PELModuli.CMPoints.Splitting.exists_simultaneously_split_prime hSplitPrimes fields excluded
    (max bound (max M.goodReductionBound (max dN dE)))
  let : Fact q.Prime := ⟨hq⟩
  have hb' : max M.goodReductionBound (max dN dE) < q :=
    lt_of_le_of_lt (le_max_right _ _) hb
  have hd : max dN dE < q := lt_of_le_of_lt (le_max_right _ _) hb'
  have hN : PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt N q := hs (true, false)
  obtain ⟨fN⟩ := hdN q (lt_of_le_of_lt (le_max_left _ _) hd) hN
  refine ⟨q, hq, lt_of_le_of_lt (le_max_left _ _) hb, hx,
    hs (false, false), hs (false, true), PELModuli.CMPoints.Splitting.complete_splitting_descends iN q hN, ?_, ?_, ?_⟩
  · intro u
    exact PELModuli.CMPoints.Splitting.complete_splitting_descends
      (ComplexMultiplication.CommonCMField.CM.conjugateCompositum.embedding L u (IsAlgClosed.lift : L u →ₐ[ℚ] ℂ)).toRingHom q (hs (true, true))
  · intro u
    exact PELModuli.CMPoints.Splitting.complete_splitting_descends (iC.comp (eF u)) q hN
  · intro jC ι
    let g := ι.comp (CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure jC M.arithmetic.embedding).toRingHom
    let f : N →+* ℚ_[q] := fN.comp
      (GaloisDiscrete.ParameterChoices.embeddingAutEquiv ((algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp fN)
        (CompatibleQadicChoice.ParameterChoices.extendLocalFieldEmbedding iN g).toRatAlgHom).toRingHom
    let j := CompatibleQadicChoice.ParameterChoices.normalExtensionQadicChoice M.arithmetic.embedding jC ι iN fN
    refine ⟨j, fun u => f.comp (iC.comp (eF u)), rfl, rfl, rfl, ?_,
      hdE _ _ _ q j (lt_of_le_of_lt (le_max_right _ _) hd),
      ⟨M.goodIntegralReduction_of_large_prime hM j (lt_of_le_of_lt (le_max_left _ _) hb')⟩⟩
    intro u
    calc
      _ = f.comp (iC.comp ((eF u).comp (iF u))) := rfl
      _ = f.comp (iC.comp iB) := congrArg (fun h => f.comp (iC.comp h)) (hc u)
      _ = _ := (CompatibleQadicChoice.ParameterChoices.qadicChoiceInChosenClosure_embedding M.arithmetic.embedding jC ι
        (CompatibleQadicChoice.ParameterChoices.normalExtensionPadicEmbedding iN g fN) (CompatibleQadicChoice.ParameterChoices.normalExtensionPadicEmbedding_spec iN g fN)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedClosurePointPrime.ParameterChoices
