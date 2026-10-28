import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsArithmeticQuotientExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.QuotientGeneric

/-! # Arithmetic Compared Quotient Existence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticComparedQuotientExistence.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.QuotientGeneric.ArithmeticPELComparison

theorem exists_arithmetic_compared_prime_pel_quotient
    (h43 : ReferenceFamily.ModuliInput)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K] (iota : E →+* K) (κ : K →+* ℂ)
    (hemb : κ.comp iota = P.μ) (N : ℕ) (hN : 3 ≤ N)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    ∃ B : Base.ArithmeticBaseExtension K κ, IsUnit (N : B.R) ∧
      ∃ p : ℕ, ∃ hp : p.Prime, 3 ≤ p ∧ Nat.Coprime p N ∧
        Nat.Coprime p (∏ i, P.polarizationType i) ∧ IsUnit (p : B.R) ∧
        let _ : Fact p.Prime := ⟨hp⟩
        ∃ V : Over B.base, ∃ hred : IsReduced V.left, let _ : IsReduced V.left := hred
          IsNoetherian V.left ∧ LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom ∧
          ∃ U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V,
            ∃ hU : U.IsFine, U.PrescribedRigid ∧
              (∃ e : (Over.pullback B.generic).obj V ≅ Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p,
                Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeUniversal B M p).pullback e.hom)
                  (U.genericIntegralFamily B iota))) ∧
              ∃ (Q : Over B.base) (π : V ⟶ Q),
                IsReduced Q.left ∧ IsNoetherian Q.left ∧
                LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧
                IsFinite π.left ∧ Etale π.left ∧ Surjective π.left ∧
                IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source V (3 * s) p).left
                  (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left ∧
                (∃ d : (Over.pullback B.generic).obj Q ≅ Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M,
                  Nonempty (PEL.Iso.PolarizedActionIso
                    ((Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).pullback
                      ((Over.pullback B.generic).map π ≫ d.hom)).data
                    (U.genericIntegralFamily B iota).forgetAuxiliary.data)) ∧
                ∀ (T : Over B.base) (f : V ⟶ T),
                  IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source V (3 * s) p ≫ f =
                    IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU ≫ f →
                  ∃! q : Q ⟶ T, π ≫ q = f := by
  obtain ⟨B, hNB, p, hp, hp3, hpN, hpδ, hpB, V, hr, hn, hft, hqc, hsep,
      U, hU, hrigid, hcomp, Q, π, hrQ, hnQ, hftQ, hqcQ, hf, ht, hsπ, hk, hquot⟩ :=
    ModelsArithmeticQuotientExistence.FromPrimeModels.exists_arithmetic_prime_pel_quotient h43 hPresentations
      s hs hdegree P hP iota κ hemb N hN M hM
  have : Fact p.Prime := ⟨hp⟩
  have : IsReduced V.left := hr
  have : IsFinite π.left := hf
  have : Etale π.left := ht
  have : Surjective π.left := hsπ
  obtain ⟨e, ⟨a⟩⟩ := hcomp
  exact ⟨B, hNB, p, hp, hp3, hpN, hpδ, hpB, V, hr, hn, hft, hqc, hsep,
    U, hU, hrigid, ⟨e, ⟨a⟩⟩, Q, π, hrQ, hnQ, hftQ, hqcQ, hf, ht, hsπ, hk,
    Arithmetic.QuotientGeneric.ArithmeticPELComparison.quotient_generic_comparison B M hM U hU π hk e a, hquot⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticComparedQuotientExistence.FromPrimeModels
