import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PrimeModels

/-! # Models Existence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsExistence.FromPrimeModels

noncomputable section

/-! The exact arithmetic prime model supplied for the fixed PEL datum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_arithmetic_prime_added_pel_fine_model
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] (κ : K →+* ℂ)
    {s N : ℕ} [NeZero N] (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hs : 0 < s)
    (hδ : ∀ i, 0 < P.polarizationType i)
    (hchain : ∀ i j, i ≤ j → P.polarizationType i ∣ P.polarizationType j)
    (iota : E →+* K) (_hE34 : Presentations.Hilbert.EndomorphismEquationsInput.{0}) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    ∃ B : Base.ArithmeticBaseExtension K κ, IsUnit (N : B.R) ∧
      ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ Nat.Coprime p N ∧
        Nat.Coprime p (∏ i, P.polarizationType i) ∧ IsUnit (p : B.R) ∧
        ∃ V : Over B.base, IsReduced V.left ∧ IsNoetherian V.left ∧
          LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom ∧
          ∃ U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V,
            ∀ (T : Over B.base) [IsReduced T.left]
              (A : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N T),
              ∃! f : T ⟶ V, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback f) A) := by
  exact Arithmetic.PrimeModels.ArithmeticPrimePELModels.exists_model κ hs hδ hchain iota

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsExistence.FromPrimeModels
