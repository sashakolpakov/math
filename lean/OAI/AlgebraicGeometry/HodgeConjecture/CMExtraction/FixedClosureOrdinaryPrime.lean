import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedClosurePointPrime
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ReductionOrdinary

/-! # Fixed Closure Ordinary Prime -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedClosureOrdinaryPrime.Ordinary

noncomputable section

/-! Construct ordinary points on every geometric component while retaining
any subsequently selected comparison closure, at the same chosen prime. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedClosurePointPrime.ParameterChoices

theorem exists_fixed_closure_ordinary_component_prime
    (hSplitPrimes : PELModuli.CMPoints.Arithmetic.SplitPrimesInput)
    (hHilb : PELModuli.IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : PELModuli.IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hCMAbelianVarietyA : PELModuli.CMPoints.Descent.AbelianInput) (hCMAbelianVarietyM : PELModuli.CMPoints.Descent.ModuliInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    {Idx : Type} [Finite Idx]
    (L : Idx → Type) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt E q ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt K q ∧
      PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧ (∀ i, PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt (L i) q) ∧
      ∀ (jC : ParameterChoices.Qbar →+* ℂ) (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q]),
      ∃ j : M.QadicChoice q,
        j.complexClosure = jC ∧ j.iota = ι ∧
        j.fieldInClosure = (CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure jC M.arithmetic.embedding).toRingHom ∧
        j.HasSplitCoordinates M.extendedEmbedding ∧
        ∃ R : M.GoodIntegralReduction q j,
          ∀ (a : M.Family) (t : Fin (M.componentCount a)),
            ∃ y : (R.geometricComponent a t).left,
              R.IsOrdinary a ((R.geometricComponentInclusion a t).left y) := by
  classical
  let I := (a : M.Family) × Fin (M.componentCount a)
  let C (u : I) := Classical.choice
    (M.exists_CM_spread_data hHilb hEnd hCMAbelianVarietyA hCMAbelianVarietyM hM u.1 u.2)
  let T (u : I) := Classical.choice (C u).exists_integral_component_data
  choose D hD hordinary using fun u : I => (T u).exists_ordinary_bound
  let B := ∑ u : I, (D u + (T u).denominator)
  obtain ⟨dSplit, hdSplit⟩ := PELModuli.CMPoints.SplitCoordinates.exists_split_coordinates_bound E
  let F (u : I) := (T u).base.extension.carrier
  let iF (u : I) : M.arithmetic.extension.carrier →+* F u := (C u).originalFieldEmbedding
  obtain ⟨q, hq, hb, hx, hE, hK, hBase, hL, _, hchoices⟩ :=
    FixedClosurePointPrime.ParameterChoices.exists_fixed_closure_point_field_prime hSplitPrimes M hM F iF L excluded
      (max bound (max dSplit B))
  let : Fact q.Prime := ⟨hq⟩
  refine ⟨q, hq, lt_of_le_of_lt (le_max_left _ _) hb, hx, hE, hK, hBase, hL, ?_⟩
  intro jC ι
  obtain ⟨j, fF, hJC, hJI, hJF, hfF, hsplit, ⟨R⟩⟩ := hchoices jC ι
  have hlarge : max dSplit B < q := lt_of_le_of_lt (le_max_right _ _) hb
  have hB : B < q := lt_of_le_of_lt (le_max_right _ _) hlarge
  have hsum (u : I) : D u + (T u).denominator ≤ B :=
    Finset.single_le_sum (fun v _ => Nat.zero_le (D v + (T v).denominator)) (Finset.mem_univ u)
  have hbound (u : I) : D u < q :=
    lt_of_le_of_lt ((Nat.le_add_right _ _).trans (hsum u)) hB
  have hden (u : I) : (T u).denominator < q :=
    lt_of_le_of_lt ((Nat.le_add_left _ _).trans (hsum u)) hB
  have hcop (u : I) : q.Coprime (T u).base.denominator :=
    hq.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (T u).denominator_ne_zero) (hden u))
  let jT (u : I) := PELModuli.CMPoints.LocalPadic.qadicChoiceOfEmbedding (T u).base.embedding (fF u)
  have hjT (u : I) : (jT u).HasSplitCoordinates (C u).coefficientEmbedding :=
    hdSplit _ _ _ q (jT u) (lt_of_le_of_lt (le_max_left _ _) hlarge)
  have hf (u : I) : ((jT u).completion.toRingHom.comp
      (NumberField.FinitePlace.embedding (jT u).prime)).comp (C u).originalFieldEmbedding =
        j.completion.toRingHom.comp (NumberField.FinitePlace.embedding j.prime) :=
    (congrArg (fun f => f.comp (C u).originalFieldEmbedding)
      (PELModuli.CMPoints.CompatiblePrime.qadicChoiceOfEmbedding_generic (T u).base.embedding (fF u))).trans (hfF u)
  refine ⟨j, hJC, hJI, hJF, hsplit, R, ?_⟩
  intro a t
  let u : I := ⟨a, t⟩
  let x₀ := IsLocalRing.closedPoint (AlgebraicClosure (ZMod q))
  let y := (T u).componentPoint R (jT u) (hcop u) (hf u) x₀
  refine ⟨y, ?_⟩
  have hgood : q.Coprime (∏ i, (M.datum a).polarizationType i) :=
    (R.polarizationPrimeToQ a).of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0))
  have hc := hordinary u q hq (jT u) (hjT u) (hbound u) hgood
  have ho := (T u).isOrdinary_of_integral_section_counts R (jT u) (hcop u) (hf u) hc
    ((T u).familyPoint R (jT u) (hcop u) (hf u) x₀) ⟨x₀, rfl⟩
  exact (show (T u).familyPoint R (jT u) (hcop u) (hf u) x₀ =
    (R.geometricComponentInclusion a t).left y from Scheme.Hom.comp_apply _ _ _ ) ▸ ho

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedClosureOrdinaryPrime.Ordinary
