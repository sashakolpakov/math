import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReducedFamily
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.ReducedClassification

/-! # Reduced Fine -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReducedFine

noncomputable section

/-! The actual full PEL family over the collapsed arithmetic base is
fine on every reduced test scheme, with its original coefficient embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s p N : ℕ} [NeZero p] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    {X Q : Over B.base} [IsReduced X.left] [IsLocallyNoetherian X.left]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) p).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left}

theorem arithmetic_reduced_pel_family_classifies
    (D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding) (φ : B.R →+* D.R)
    (hφ : D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField)
    (A : U.PrescribedAbelianPair hU π hk (Spec.map (CommRingCat.ofHom φ)))
    (hrigid : U.PrescribedRigid) (hp : p.Prime) (hunit : IsUnit (p : B.R))
    (T : Over (B.compose D).base) [IsReduced T.left]
    (C : PEL.Has.IntegralPELObject P (B.compose D).R ((B.compose D).integralEmbedding iota) N T) :
    ∃! f : T ⟶ Reduction.reduction ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q),
      Nonempty (PEL.Iso.PolarizedActionIso ((ReducedFamily.arithmetic_reduced_pel_family B D φ hφ A hrigid).pullback f).data
        C.data) := by
  have := ReducedFamily.arithmetic_scalar_parameter_isNoetherian B (Q := Q) D φ
  let C₀ : PEL.Has.IntegralPELObject P D.R (φ.comp (B.integralEmbedding iota)) N T := {
    data := C.data
    rosati := C.rosati
    lieRanks := (B.compose_integralEmbedding D φ hφ iota).symm ▸ C.lieRanks }
  exact A.reducedPELObject_classifies φ hrigid hp hunit T C₀

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReducedFine
