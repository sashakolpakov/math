import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReferenceComparison

/-! # Models Arithmetic Compared Existence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsArithmeticComparedExistence.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_arithmetic_prime_compared_pel_fine_model
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] (κ : K →+* ℂ)
    {s N : ℕ} [NeZero N] (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hs : 0 < s)
    (hδ : ∀ i, 0 < P.polarizationType i)
    (hchain : ∀ i j, i ≤ j → P.polarizationType i ∣ P.polarizationType j)
    (iota : E →+* K) (hN : 3 ≤ N) (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
     (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    ∃ B : Base.ArithmeticBaseExtension K κ, IsUnit (N : B.R) ∧
      ∃ p : ℕ, ∃ hp : p.Prime, 3 ≤ p ∧ Nat.Coprime p N ∧
        Nat.Coprime p (∏ i, P.polarizationType i) ∧ IsUnit (p : B.R) ∧
        let _ : Fact p.Prime := ⟨hp⟩
        ∃ V : Over B.base, IsReduced V.left ∧ IsNoetherian V.left ∧
          LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom ∧
          ∃ U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V,
            (∀ (T : Over B.base) [IsReduced T.left]
              (A : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N T),
              ∃! f : T ⟶ V, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback f) A)) ∧
            ∃ e : (Over.pullback B.generic).obj V ≅ Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p,
              Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeUniversal B M p).pullback e.hom)
                (U.genericIntegralFamily B iota)) := by
  obtain ⟨B, hBN, p, hp, hp3, hpN, hpδ, hpB, V, hr, hn, hft, hqc, hsep, U, hclass⟩ :=
    ModelsExistence.FromPrimeModels.exists_arithmetic_prime_added_pel_fine_model (N := N) κ P hs hδ hchain iota hPresentations
  have : Fact p.Prime := ⟨hp⟩
  have : IsReduced V.left := hr
  have : LocallyOfFiniteType V.hom := hft
  have : QuasiCompact V.hom := hqc
  exact ⟨B, hBN, p, hp, hp3, hpN, hpδ, hpB, V, hr, hn, hft, hqc, hsep, U, hclass,
    Arithmetic.ReferenceComparison.arithmetic_pel_reference_comparison B iota U hclass M hM hN hPresentations⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsArithmeticComparedExistence.FromPrimeModels
