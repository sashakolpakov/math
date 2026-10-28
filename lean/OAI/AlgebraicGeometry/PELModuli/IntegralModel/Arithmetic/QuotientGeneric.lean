import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericProjection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.QuotientScalarFibers
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleQuotientComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FineMapFibers
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericReduced
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization

/-! # Quotient Generic -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.QuotientGeneric.ArithmeticPELComparison

noncomputable section

/-! The actual arithmetic quotient has the given reduced ReferenceFamily model as
its generic fiber. The comparison is constructed from the two finite
etale covers and identifies their actual universal PEL families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N p : ℕ} [Fact p.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) {V Q : Over B.base}
    [IsReduced V.left]

include hM in
theorem quotient_generic_comparison
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V) (hU : U.IsFine)
    (π : V ⟶ Q) [IsFinite π.left] [Etale π.left] [Surjective π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source V (3 * s) p).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)
    (e : (Over.pullback B.generic).obj V ≅ ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p)
    (a : IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((ReferencePrimeFrame.ArithmeticPELComparison.primeUniversal B M p).pullback e.hom)
      (U.genericIntegralFamily B iota)) :
    ∃ d : (Over.pullback B.generic).obj Q ≅ ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M,
      Nonempty (PEL.Iso.PolarizedActionIso
        ((ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).pullback ((Over.pullback B.generic).map π ≫ d.hom)).data
        (U.genericIntegralFamily B iota).forgetAuxiliary.data) := by
  obtain ⟨q, hf, ht, hs, ⟨eq⟩⟩ := GenericProjection.ArithmeticPELComparison.generic_prescribed_projection B M U e a
  have : IsFinite q.left := hf
  have : Etale q.left := ht
  have : Surjective q.left := hs
  let π' := (Over.pullback B.generic).map π
  have : IsFinite π'.left := MorphismProperty.of_isPullback (Specialization.base_change_square B.generic π)
    (inferInstanceAs (IsFinite π.left))
  have : Etale π'.left := MorphismProperty.of_isPullback (Specialization.base_change_square B.generic π)
    (inferInstanceAs (Etale π.left))
  have : Surjective π'.left := MorphismProperty.of_isPullback (Specialization.base_change_square B.generic π)
    (inferInstanceAs (Surjective π.left))
  have : IsReduced ((Over.pullback B.generic).obj V).left := B.genericFiber_isReduced V
  have hA := Reduced.Generic.reduced_generic_finePEL_action_classifies (algebraMap K B.extension.carrier) M hM
  obtain ⟨d, hd⟩ := Finite.EtaleQuotientComparison.finite_etale_quotient_iso π' q (fun T _ f g =>
    (IntegralAuxiliary.QuotientScalarFibers.IntegralAuxiliaryAction.scalar_quotient_eq_iff_prescribed_iso U hU π hk B.toField T f g).trans
      (FineMapFibers.finePEL_map_eq_iff_prescribed_iso (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M)
        (U.genericIntegralFamily B iota).forgetAuxiliary hA q eq f g).symm)
  exact ⟨d, ⟨(PEL.Iso.PolarizedActionIso.pullbackCongr (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).data _ _
    (congrArg Over.Hom.left hd)).trans eq⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.QuotientGeneric.ArithmeticPELComparison
