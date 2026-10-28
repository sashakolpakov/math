import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReferenceComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.PELFrameGeometry

/-! # Generic Projection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericProjection.ArithmeticPELComparison

noncomputable section

/-! The given comparison to the actual prime-frame universal family
induces a finite etale prescribed-level projection with its full PEL
family comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N p : ℕ} [Fact p.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) {V : Over B.base}

theorem generic_prescribed_projection
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V)
    (e : (Over.pullback B.generic).obj V ≅ ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p)
    (a : IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((ReferencePrimeFrame.ArithmeticPELComparison.primeUniversal B M p).pullback e.hom)
      (U.genericIntegralFamily B iota)) :
    ∃ q : (Over.pullback B.generic).obj V ⟶ ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M,
      IsFinite q.left ∧ Etale q.left ∧ Surjective q.left ∧
      Nonempty (PEL.Iso.PolarizedActionIso ((ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).pullback q).data
        (U.genericIntegralFamily B iota).forgetAuxiliary.data) := by
  let f := IntegralPEL.FrameExistence.IntegralPELFrame.forget (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M) (ReferencePrimeFrame.ArithmeticPELComparison.primeUnit B M p)
  obtain ⟨hf, ht, hs⟩ := IntegralPEL.PELFrameGeometry.IntegralPELFrame.finite_etale_surjective
    (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M) (ReferencePrimeFrame.ArithmeticPELComparison.primeUnit B M p) (Fact.out : p.Prime)
  have : IsFinite f.left := hf
  have : Etale f.left := ht
  have : Surjective f.left := hs
  have : IsIso e.hom.left := ((Over.forget (Spec (.of B.extension.carrier))).mapIso e).isIso_hom
  refine ⟨e.hom ≫ f, inferInstanceAs (IsFinite (e.hom.left ≫ f.left)),
    inferInstanceAs (Etale (e.hom.left ≫ f.left)),
    inferInstanceAs (Surjective (e.hom.left ≫ f.left)), ?_⟩
  exact ⟨(PEL.Iso.PolarizedActionIso.pullbackComp (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).data f.left e.hom.left).symm.trans
    a.forgetAuxiliary⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericProjection.ArithmeticPELComparison
