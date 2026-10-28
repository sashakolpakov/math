import OAI.AlgebraicGeometry.PELModuli.CMPoints.PrimeChoice
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CommonEmbeddedFields

/-! # Compatible Prime -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CompatiblePrime

noncomputable section

/-! Choose the q-adic embedding on a larger number field first. This
retains compatibility with fields of definition of finitely many points. -/

theorem qadicChoiceOfEmbedding_generic
    {F : Type} [Field F] [NumberField F]
    {q : ℕ} [Fact q.Prime] (κ : F →+* ℂ) (f : F →+* Padic q) :
    (LocalPadic.qadicChoiceOfEmbedding κ f).completion.toRingHom.comp
      (NumberField.FinitePlace.embedding (LocalPadic.qadicChoiceOfEmbedding κ f).prime) = f :=
  LocalPadic.embeddingCompletionEquiv_comp f

/-- A common prime with a compatible embedding of an additional number
field. The extra field can contain all the chosen CM points and actions. -/
theorem exists_common_good_split_qadic_prime_with_extension
    (hSplitPrimes : Arithmetic.SplitPrimesInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    (F : Type) [Field F] [NumberField F]
    (iF : M.arithmetic.extension.carrier →+* F)
    {Idx : Type*} [Finite Idx]
    (L : Idx → Type*) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧
      Arithmetic.SplitsCompletelyAt E q ∧ Arithmetic.SplitsCompletelyAt K q ∧
      Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧
      (∀ i, Arithmetic.SplitsCompletelyAt (L i) q) ∧ Arithmetic.SplitsCompletelyAt F q ∧
      ∃ (j : M.QadicChoice q) (fF : F →+* Padic q),
        fF.comp iF = j.completion.toRingHom.comp
          (NumberField.FinitePlace.embedding j.prime) ∧
        j.HasSplitCoordinates M.extendedEmbedding ∧ Nonempty (M.GoodIntegralReduction q j) := by
  let C := ComplexMultiplication.CommonCMField.CM.conjugateCompositum L
  let fields : Bool × Bool → Type
    | (false, false) => E
    | (false, true) => K
    | (true, false) => F
    | (true, true) => C
  let fieldStructures : ∀ i, Field (fields i)
    | (false, false) => inferInstanceAs (Field E)
    | (false, true) => inferInstanceAs (Field K)
    | (true, false) => inferInstanceAs (Field F)
    | (true, true) => inferInstanceAs (Field C)
  let numberFields : ∀ i, NumberField (fields i)
    | (false, false) => inferInstanceAs (NumberField E)
    | (false, true) => inferInstanceAs (NumberField K)
    | (true, false) => inferInstanceAs (NumberField F)
    | (true, true) => inferInstanceAs (NumberField C)
  obtain ⟨dF, hdF⟩ := LocalPadic.exists_padic_embedding_bound F
  obtain ⟨dE, hdE⟩ := SplitCoordinates.exists_split_coordinates_bound E
  obtain ⟨q, hq, hb, hx, hs⟩ := Splitting.exists_simultaneously_split_prime hSplitPrimes fields excluded
    (max bound (max M.goodReductionBound (max dF dE)))
  let : Fact q.Prime := ⟨hq⟩
  have hb' : max M.goodReductionBound (max dF dE) < q :=
    lt_of_le_of_lt (le_max_right _ _) hb
  have hds : max dF dE < q := lt_of_le_of_lt (le_max_right _ _) hb'
  have hF : Arithmetic.SplitsCompletelyAt F q := hs (true, false)
  obtain ⟨fF⟩ := hdF q (lt_of_le_of_lt (le_max_left _ _) hds) hF
  let j := LocalPadic.qadicChoiceOfEmbedding M.arithmetic.embedding (fF.comp iF)
  refine ⟨q, hq, lt_of_le_of_lt (le_max_left _ _) hb, hx,
    hs (false, false), hs (false, true), Splitting.complete_splitting_descends iF q hF,
    ?_, hF, j, fF, (qadicChoiceOfEmbedding_generic _ _).symm,
    hdE _ _ _ q j (lt_of_le_of_lt (le_max_right _ _) hds),
    ⟨M.goodIntegralReduction_of_large_prime hM j
      (lt_of_le_of_lt (le_max_left _ _) hb')⟩⟩
  intro i
  let σ : L i →ₐ[ℚ] ℂ := IsAlgClosed.lift
  exact Splitting.complete_splitting_descends
    (ComplexMultiplication.CommonCMField.CM.conjugateCompositum.embedding L i σ).toRingHom q (hs (true, true))

/-- Choose one prime and mutually compatible q-adic embeddings for any
finite collection of point fields over the prescribed arithmetic base. -/
theorem exists_common_good_split_prime_for_point_fields
    (hSplitPrimes : Arithmetic.SplitPrimesInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    {PointIdx : Type*} [Finite PointIdx] (F : PointIdx → Type)
    [∀ i, Field (F i)] [∀ i, NumberField (F i)]
    (iF : ∀ i, M.arithmetic.extension.carrier →+* F i)
    {Idx : Type*} [Finite Idx]
    (L : Idx → Type*) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧
      Arithmetic.SplitsCompletelyAt E q ∧ Arithmetic.SplitsCompletelyAt K q ∧
      Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧
      (∀ i, Arithmetic.SplitsCompletelyAt (L i) q) ∧ (∀ i, Arithmetic.SplitsCompletelyAt (F i) q) ∧
      ∃ (j : M.QadicChoice q) (fF : ∀ i, F i →+* Padic q),
        (∀ i, (fF i).comp (iF i) = j.completion.toRingHom.comp
          (NumberField.FinitePlace.embedding j.prime)) ∧
        j.HasSplitCoordinates M.extendedEmbedding ∧ Nonempty (M.GoodIntegralReduction q j) := by
  obtain ⟨C, hC, iB, eF, _, hc⟩ :=
    CommonEmbeddedFields.exists_compatible_common_field M.arithmetic.embedding F iF
  let : NumberField C := hC
  obtain ⟨q, hq, hb, hx, he, hk, hB, hL, hCsplit, j, fC, hfC, hs, hR⟩ :=
    exists_common_good_split_qadic_prime_with_extension hSplitPrimes M hM C iB L excluded bound
  let : Fact q.Prime := ⟨hq⟩
  refine ⟨q, hq, hb, hx, he, hk, hB, hL,
    fun i => Splitting.complete_splitting_descends (eF i) q hCsplit,
    j, fun i => fC.comp (eF i), ?_, hs, hR⟩
  intro i
  rw [RingHom.comp_assoc, hc i]
  exact hfC

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CompatiblePrime
