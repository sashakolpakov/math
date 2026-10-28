import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticComparedQuotientExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AbelianPair
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ReducedFineComplexAffine

/-! # Arithmetic Abelian Pair Existence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticAbelianPairExistence.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AbelianPair.ArithmeticPELComparison

theorem exists_arithmetic_pel_quotient_with_abelian_pair
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
          ∃ hn : IsNoetherian V.left, let _ : IsNoetherian V.left := hn
          LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom ∧
          ∃ U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V,
            ∃ hU : U.IsFine, U.PrescribedRigid ∧
              (∃ e : (Over.pullback B.generic).obj V ≅ Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p,
                Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeUniversal B M p).pullback e.hom)
                  (U.genericIntegralFamily B iota))) ∧
              ∃ (Q : Over B.base) (π : V ⟶ Q),
                IsReduced Q.left ∧ IsNoetherian Q.left ∧
                LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧
                ∃ hf : IsFinite π.left, let _ : IsFinite π.left := hf
                ∃ he : Etale π.left, let _ : Etale π.left := he
                Surjective π.left ∧
                ∃ hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source V (3 * s) p).left
                  (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left,
                (∃ d : (Over.pullback B.generic).obj Q ≅ Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M,
                  Nonempty (PEL.Iso.PolarizedActionIso
                    ((Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).pullback
                      ((Over.pullback B.generic).map π ≫ d.hom)).data
                    (U.genericIntegralFamily B iota).forgetAuxiliary.data)) ∧
                ∃ D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding,
                  B.denominator ∣ D.denominator ∧ ∃ φ : B.R →+* D.R,
                    D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField ∧
                    Nonempty (U.PrescribedAbelianPair hU π hk
                      (Spec.map (CommRingCat.ofHom φ))) := by
  obtain ⟨B, hNB, p, hp, hp3, hpN, hpδ, hpB, V, hr, hn, hft, hqc, hsep,
      U, hU, hrigid, hcomp, Q, π, hrQ, hnQ, hftQ, hqcQ, hf, ht, hsπ, hk, hgeneric, _⟩ :=
    ArithmeticComparedQuotientExistence.FromPrimeModels.exists_arithmetic_compared_prime_pel_quotient h43 hPresentations
      s hs hdegree P hP iota κ hemb N hN M hM
  have : Fact p.Prime := ⟨hp⟩
  have : IsReduced V.left := hr
  have : IsNoetherian V.left := hn
  have : LocallyOfFiniteType V.hom := hft
  have : QuasiCompact V.hom := hqc
  have : IsSeparated V.hom := hsep
  have : IsFinite π.left := hf
  have : Etale π.left := ht
  have : Surjective π.left := hsπ
  obtain ⟨e, ⟨a⟩⟩ := hcomp
  obtain ⟨_, hAFM⟩ := ReducedFineComplexAffine.FromPrimeModels.reduced_finePEL_complex_affine h43 hPresentations
    s hs hdegree P hP iota κ hemb N hN M hM
  have : IsNoetherian Q.left := hnQ
  have : LocallyOfFiniteType Q.hom := hftQ
  have : QuasiCompact Q.hom := hqcQ
  have hV : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism V.hom :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hQ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Q.hom :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨d, ⟨ag⟩⟩ := hgeneric
  exact ⟨B, hNB, p, hp, hp3, hpN, hpδ, hpB, V, hr, hn, hft, hqc, hsep,
    U, hU, hrigid, ⟨e, ⟨a⟩⟩, Q, π, hrQ, hnQ, hftQ, hqcQ, hf, ht, hsπ, hk,
    ⟨d, ⟨ag⟩⟩, Arithmetic.AbelianPair.ArithmeticPELComparison.prescribed_arithmetic_abelian_pair B M U hU hrigid π hk hV hQ e hAFM d ag⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticAbelianPairExistence.FromPrimeModels
