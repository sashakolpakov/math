import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic
import OAI.AlgebraicGeometry.PELModuli.CMPoints.GoodReduction
import OAI.AlgebraicGeometry.PELModuli.CMPoints.SplitCoordinates

/-! # Prime Choice -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.PrimeChoice

noncomputable section

/-! One SplitPrimes application produces the common prime, the literal q-adic
choice, and an actual good reduction for every member of the finite family. -/

theorem exists_common_good_qadic_prime
    (hSplitPrimes : Arithmetic.SplitPrimesInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    {Idx : Type*} [Finite Idx]
    (L : Idx → Type*) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧
      Arithmetic.SplitsCompletelyAt E q ∧ Arithmetic.SplitsCompletelyAt K q ∧
      Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧
      (∀ i, Arithmetic.SplitsCompletelyAt (L i) q) ∧
      ∃ j : M.QadicChoice q, Nonempty (M.GoodIntegralReduction q j) := by
  let C := ComplexMultiplication.CommonCMField.CM.conjugateCompositum L
  let fields : Bool × Bool → Type
    | (false, false) => E
    | (false, true) => K
    | (true, false) => M.arithmetic.extension.carrier
    | (true, true) => C
  let fieldStructures : ∀ i, Field (fields i)
    | (false, false) => inferInstanceAs (Field E)
    | (false, true) => inferInstanceAs (Field K)
    | (true, false) => inferInstanceAs (Field M.arithmetic.extension.carrier)
    | (true, true) => inferInstanceAs (Field C)
  let numberFields : ∀ i, NumberField (fields i)
    | (false, false) => inferInstanceAs (NumberField E)
    | (false, true) => inferInstanceAs (NumberField K)
    | (true, false) => inferInstanceAs (NumberField M.arithmetic.extension.carrier)
    | (true, true) => inferInstanceAs (NumberField C)
  obtain ⟨d, hd⟩ := LocalPadic.exists_qadicChoice_bound M.arithmetic.embedding
  obtain ⟨q, hq, hb, hx, hs⟩ := Splitting.exists_simultaneously_split_prime hSplitPrimes fields excluded
    (max bound (max M.goodReductionBound d))
  let : Fact q.Prime := ⟨hq⟩
  have he : Arithmetic.SplitsCompletelyAt E q := by
    exact hs (false, false)
  have hk : Arithmetic.SplitsCompletelyAt K q := by
    exact hs (false, true)
  have hbfield : Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q := by
    exact hs (true, false)
  have hc : Arithmetic.SplitsCompletelyAt C q := by
    exact hs (true, true)
  have hlarge : max M.goodReductionBound d < q := lt_of_le_of_lt (le_max_right _ _) hb
  obtain ⟨j⟩ := hd q (lt_of_le_of_lt (le_max_right _ _) hlarge) hbfield
  refine ⟨q, hq, lt_of_le_of_lt (le_max_left _ _) hb, hx, he, hk, hbfield, ?_,
    j, ⟨M.goodIntegralReduction_of_large_prime hM j
      (lt_of_le_of_lt (le_max_left _ _) hlarge)⟩⟩
  intro i
  let σ : L i →ₐ[ℚ] ℂ := IsAlgClosed.lift
  exact Splitting.complete_splitting_descends
    (ComplexMultiplication.CommonCMField.CM.conjugateCompositum.embedding L i σ).toRingHom q hc

/-- The complete arithmetic prefix of CMPoints, including the prescribed
embedding labels at every q-power. -/
theorem exists_common_good_split_qadic_prime
    (hSplitPrimes : Arithmetic.SplitPrimesInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    {Idx : Type*} [Finite Idx]
    (L : Idx → Type*) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧
      Arithmetic.SplitsCompletelyAt E q ∧ Arithmetic.SplitsCompletelyAt K q ∧
      Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧
      (∀ i, Arithmetic.SplitsCompletelyAt (L i) q) ∧
      ∃ j : M.QadicChoice q,
        j.HasSplitCoordinates M.extendedEmbedding ∧ Nonempty (M.GoodIntegralReduction q j) := by
  obtain ⟨d, hd⟩ := SplitCoordinates.exists_split_coordinates_bound E
  obtain ⟨q, hq, hb, hx, he, hk, hf, hl, j, hR⟩ :=
    exists_common_good_qadic_prime hSplitPrimes M hM L excluded (max bound d)
  let : Fact q.Prime := ⟨hq⟩
  exact ⟨q, hq, lt_of_le_of_lt (le_max_left _ _) hb, hx, he, hk, hf, hl, j,
    hd M.arithmetic.extension.carrier M.arithmetic.embedding M.extendedEmbedding q j
      (lt_of_le_of_lt (le_max_right _ _) hb), hR⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.PrimeChoice
