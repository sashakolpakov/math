import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AddedFromPure

/-! # Prime Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PrimeModels

noncomputable section

/-! The exact arithmetic prime-level model used by the later IntegralModel
constructions. This local input concerns one fixed PEL datum and retains
the original family and classification on every reduced test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

class ArithmeticPrimePELModels
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) : Prop where
  exists_model : ∀ {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
    {N : ℕ} [NeZero N] (_hs : 0 < s)
    (_hδ : ∀ i, 0 < P.polarizationType i)
    (_hchain : ∀ i j, i ≤ j → P.polarizationType i ∣ P.polarizationType j)
    (iota : E →+* K),
    ∃ B : Base.ArithmeticBaseExtension K κ, IsUnit (N : B.R) ∧
      ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ Nat.Coprime p N ∧
        Nat.Coprime p (∏ i, P.polarizationType i) ∧ IsUnit (p : B.R) ∧
        ∃ V : Over B.base, IsReduced V.left ∧ IsNoetherian V.left ∧
          LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom ∧
          ∃ U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V,
            ∀ (T : Over B.base) [IsReduced T.left]
              (A : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N T),
              ∃! f : T ⟶ V, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback f) A)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PrimeModels
