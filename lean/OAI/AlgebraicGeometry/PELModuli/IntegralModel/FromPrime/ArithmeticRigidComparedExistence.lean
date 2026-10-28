import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.RigidAddedFine
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReferenceComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Relation

/-! # Arithmetic Rigid Compared Existence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticRigidComparedExistence.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_arithmetic_prime_rigid_compared_pel_fine_model
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
            U.IsFine ∧ U.PrescribedRigid ∧
            ∃ e : (Over.pullback B.generic).obj V ≅ Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p,
              Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeUniversal B M p).pullback e.hom)
                (U.genericIntegralFamily B iota)) := by
  obtain ⟨B, _, p, hp, hp3, hpN, hpδ, hpB, X, hr, hn, hft, hqc, hsep, U, hclass⟩ :=
    ModelsExistence.FromPrimeModels.exists_arithmetic_prime_added_pel_fine_model (N := N) κ P hs hδ hchain iota hPresentations
  have : Fact p.Prime := ⟨hp⟩
  have : IsReduced X.left := hr
  have : IsNoetherian X.left := hn
  have : LocallyOfFiniteType X.hom := hft
  have : QuasiCompact X.hom := hqc
  have : IsSeparated X.hom := hsep
  obtain ⟨D, hD, hND, _, φ, _, V, hrV, hnV, hftV, hqcV, hsepV, A, hA, hRigid⟩ :=
    Arithmetic.RigidAddedFine.exists_arithmetic_rigid_added_pel_fine_model B iota U hclass hN hPresentations
  let B' := B.withDenominator D hD
  have hpB' : IsUnit (p : B'.R) := by simpa only [map_natCast] using hpB.map φ
  have : IsReduced V.left := hrV
  have : LocallyOfFiniteType V.hom := hftV
  have : QuasiCompact V.hom := hqcV
  exact ⟨B', B'.divisor_isUnit N hND, p, hp, hp3, hpN, hpδ, hpB', V,
    hrV, hnV, hftV, hqcV, hsepV, A, hA, hRigid,
    Arithmetic.ReferenceComparison.arithmetic_pel_reference_comparison B' iota A hA M hM hN hPresentations⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticRigidComparedExistence.FromPrimeModels
