import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticRigidComparedExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexAffineCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ReducedFineComplexAffine

/-! # Arithmetic Complex Covered Existence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticComplexCoveredExistence.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexAffineCover.ArithmeticPELComparison

theorem exists_arithmetic_prime_complex_covered_pel_model
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
        ∃ V : Over B.base, IsReduced V.left ∧ IsNoetherian V.left ∧
          LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom ∧
          ∃ U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V,
            ∃ hU : U.IsFine, U.PrescribedRigid ∧
              (∃ e : (Over.pullback B.generic).obj V ≅ Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p,
                Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeUniversal B M p).pullback e.hom)
                  (U.genericIntegralFamily B iota))) ∧
              let φ := B.embedding.comp B.toField
              let VC := (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj V
              let UC := U.baseChange φ
              ∃ hred : IsReduced VC.left, let _ : IsReduced VC.left := hred
                ∃ (I : Type) (_ : Finite I) (W : I → VC.left.Opens),
                  (∀ i, IsAffineOpen (W i)) ∧
                  (∀ i, (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source VC (3 * s) p).left ⁻¹ᵁ W i =
                    (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target UC
                      (IntegralAdded.FineBaseChange.integralAddedPEL_fine_baseChange U hU φ)).left ⁻¹ᵁ W i) ∧
                  iSup W = ⊤ := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨hredM, hAFM⟩ := ReducedFineComplexAffine.FromPrimeModels.reduced_finePEL_complex_affine h43 hPresentations
    s hs hdegree P hP iota κ hemb N hN M hM
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hδ, hchain, _⟩ := hP
  obtain ⟨B, hNB, p, hp, hp3, hpN, hpδ, hpB, V, hr, hn, hft, hqc, hsep, U, hU,
      hrigid, e, he⟩ := ArithmeticRigidComparedExistence.FromPrimeModels.exists_arithmetic_prime_rigid_compared_pel_fine_model
        κ P hs hδ hchain iota hN M hM hPresentations
  have : Fact p.Prime := ⟨hp⟩
  have : QuasiCompact V.hom := hqc
  have : IsSeparated V.hom := hsep
  exact ⟨B, hNB, p, hp, hp3, hpN, hpδ, hpB, V, hr, hn, hft, hqc, hsep, U,
    hU, hrigid, ⟨e, he⟩, Arithmetic.ComplexAffineCover.ArithmeticPELComparison.compared_parameter_complex_affine_cover B M U hU hrigid e hredM hAFM⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticComplexCoveredExistence.FromPrimeModels
