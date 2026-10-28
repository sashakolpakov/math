import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsArithmeticComparedExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.FieldFinitenessDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.PELFrameGeometry

/-! # Reduced Fine Finite Type -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ReducedFineFiniteType.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem reduced_finePEL_finiteness
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] (κ : K →+* ℂ)
    {s N : ℕ} [NeZero N] (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hs : 0 < s)
    (hδ : ∀ i, 0 < P.polarizationType i)
    (hchain : ∀ i j, i ≤ j → P.polarizationType i ∣ P.polarizationType j)
    (iota : E →+* K) (hN : 3 ≤ N) (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
     (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    LocallyOfFiniteType (Reduction.reduction M.space).hom ∧ QuasiCompact (Reduction.reduction M.space).hom ∧
      IsNoetherian (Reduction.reduction M.space).left := by
  obtain ⟨B, _, p, hp, _, _, _, _, V, hr, _, hft, hqc, _, U, hclass⟩ :=
    ModelsExistence.FromPrimeModels.exists_arithmetic_prime_added_pel_fine_model (N := N) κ P hs hδ hchain iota hPresentations
  have : Fact p.Prime := ⟨hp⟩
  have : IsReduced V.left := hr
  have : LocallyOfFiniteType V.hom := hft
  have : QuasiCompact V.hom := hqc
  obtain ⟨e, _⟩ := Arithmetic.ReferenceComparison.arithmetic_pel_reference_comparison B iota U hclass M hM hN hPresentations
  let W := (Over.pullback B.generic).obj V
  have : LocallyOfFiniteType W.hom := inferInstanceAs
    (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd V.hom B.generic))
  have : QuasiCompact W.hom := inferInstanceAs
    (QuasiCompact (CategoryTheory.Limits.pullback.snd V.hom B.generic))
  let q := IntegralPEL.FrameExistence.IntegralPELFrame.forget (Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M) (Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeUnit B M p)
  obtain ⟨hfin, het, hsurj⟩ := IntegralPEL.PELFrameGeometry.IntegralPELFrame.finite_etale_surjective
    (Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M) (Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.primeUnit B M p) hp
  have : IsFinite q.left := hfin
  have : Etale q.left := het
  have : Surjective q.left := hsurj
  have : IsIso e.hom.left := ((Over.forget (Spec (.of B.extension.carrier))).mapIso e).isIso_hom
  let f : W ⟶ Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M := e.hom ≫ q
  have : IsFinite f.left := inferInstanceAs (IsFinite (e.hom.left ≫ q.left))
  have : Flat f.left := inferInstanceAs (Flat (e.hom.left ≫ q.left))
  have : Surjective f.left := inferInstanceAs (Surjective (e.hom.left ≫ q.left))
  obtain ⟨hft', hqc', _⟩ := Finite.CoverType.finite_flat_cover_noetherian f
  exact B.fieldExtension_finiteness_descent (Reduction.reduction M.space) hft' hqc'

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ReducedFineFiniteType.FromPrimeModels
