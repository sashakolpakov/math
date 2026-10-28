import OAI.AlgebraicGeometry.PELModuli.CMPoints.ReductionOrdinary
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CompatiblePrime

/-! # Ordinary Component Prime -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryComponentPrime

noncomputable section

/-! One common split prime gives a constructed ordinary point on every
specified geometric component of every family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_common_good_split_prime_with_ordinary_component_points
    (hSplitPrimes : Arithmetic.SplitPrimesInput)
    (hHilb : IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0}) (hCMAbelianVarietyA : Descent.AbelianInput) (hCMAbelianVarietyM : Descent.ModuliInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    {Idx : Type*} [Finite Idx]
    (L : Idx → Type*) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧ Arithmetic.SplitsCompletelyAt E q ∧ Arithmetic.SplitsCompletelyAt K q ∧
      Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧ (∀ i, Arithmetic.SplitsCompletelyAt (L i) q) ∧
      ∃ j : M.QadicChoice q, j.HasSplitCoordinates M.extendedEmbedding ∧
        ∃ R : M.GoodIntegralReduction q j,
          ∀ (a : M.Family) (t : Fin (M.componentCount a)),
            ∃ y : (R.geometricComponent a t).left,
              R.IsOrdinary a ((R.geometricComponentInclusion a t).left y) := by
  classical
  let I := (a : M.Family) × Fin (M.componentCount a)
  let C (u : I) := Classical.choice (M.exists_CM_spread_data hHilb hEnd hCMAbelianVarietyA hCMAbelianVarietyM hM u.1 u.2)
  let T (u : I) := Classical.choice (C u).exists_integral_component_data
  choose D hD hordinary using fun u : I => (T u).exists_ordinary_bound
  let B := ∑ u : I, (D u + (T u).denominator)
  obtain ⟨dSplit, hdSplit⟩ := SplitCoordinates.exists_split_coordinates_bound E
  let F (u : I) := (T u).base.extension.carrier
  let iF (u : I) : M.arithmetic.extension.carrier →+* F u := (C u).originalFieldEmbedding
  obtain ⟨q, hq, hb, hx, hE, hK, hBase, hL, _, j, fF, hfF, hsplit, ⟨R⟩⟩ :=
    CompatiblePrime.exists_common_good_split_prime_for_point_fields hSplitPrimes M hM F iF L excluded
      (max bound (max dSplit B))
  let : Fact q.Prime := ⟨hq⟩
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
  let jT (u : I) := LocalPadic.qadicChoiceOfEmbedding (T u).base.embedding (fF u)
  have hjT (u : I) : (jT u).HasSplitCoordinates (C u).coefficientEmbedding :=
    hdSplit _ _ _ q (jT u) (lt_of_le_of_lt (le_max_left _ _) hlarge)
  have hf (u : I) : ((jT u).completion.toRingHom.comp
      (NumberField.FinitePlace.embedding (jT u).prime)).comp (C u).originalFieldEmbedding =
        j.completion.toRingHom.comp (NumberField.FinitePlace.embedding j.prime) :=
    (congrArg (fun f => f.comp (C u).originalFieldEmbedding)
      (CompatiblePrime.qadicChoiceOfEmbedding_generic (T u).base.embedding (fF u))).trans (hfF u)
  refine ⟨q, hq, lt_of_le_of_lt (le_max_left _ _) hb, hx, hE, hK, hBase, hL, j, hsplit, R, ?_⟩
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

end OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryComponentPrime
