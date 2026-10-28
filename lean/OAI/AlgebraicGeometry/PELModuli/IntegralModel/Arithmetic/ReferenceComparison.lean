import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReferencePrimeFrame
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AddedGenericFamily
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.FieldExtensionReduced
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.ReferenceFrameComparison

/-! # Reference Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReferenceComparison

noncomputable section

/-! The actual generic fiber of the integral two-level fine model is
identified with the prime-frame cover of ReferenceFamily's given universal family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s p N : ℕ} [Fact p.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} (iota : E →+* K)
    {V : Over B.base} [IsReduced V.left] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]

theorem arithmetic_pel_reference_comparison
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V)
    (hclass : ∀ (T : Over B.base) [IsReduced T.left]
      (A : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N T),
      ∃! f : T ⟶ V, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback f) A))
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) (hN : 3 ≤ N)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) :
    ∃ e : (Over.pullback B.generic).obj V ≅ ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p,
      Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((ReferencePrimeFrame.ArithmeticPELComparison.primeUniversal B M p).pullback e.hom)
        (U.genericIntegralFamily B iota)) := by
  let W := (Over.pullback B.generic).obj V
  have : Countable B.extension.carrier := AbelianScheme.TateComparison.CountableResidueFields.countable_finiteType ℚ B.extension.carrier
  have : IsReduced W.left := B.genericFiber_isReduced V
  have : LocallyOfFiniteType W.hom := inferInstanceAs
    (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd V.hom B.generic))
  have : QuasiCompact W.hom := inferInstanceAs
    (QuasiCompact (CategoryTheory.Limits.pullback.snd V.hom B.generic))
  have : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  have : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace W.hom
  have : IsNoetherian W.left := ⟨⟩
  have : IsReduced (ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M).left := B.fieldExtension_isReduced (Reduction.reduction M.space)
  exact PEL.ReferenceFrameComparison.pel_reference_frame_comparison W (U.genericIntegralFamily B iota) hN hPresentations
    (AddedGenericFamily.arithmetic_addedPEL_generic_classifies B iota U hclass) (ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M) (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M)
    (Reduced.Generic.reduced_generic_finePEL_action_classifies (algebraMap K B.extension.carrier) M hM)
    (ReferencePrimeFrame.ArithmeticPELComparison.primeUnit B M p)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReferenceComparison
