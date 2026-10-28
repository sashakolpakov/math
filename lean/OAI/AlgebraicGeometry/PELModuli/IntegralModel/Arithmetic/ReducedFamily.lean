import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairReducedObject
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.TowerEmbedding

/-! # Reduced Family -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReducedFamily

noncomputable section

/-! The constructed arithmetic abelian pair gives an actual full PEL
family on the reduced scalar quotient over the collapsed arithmetic base.
The base is proved noetherian from its finite-type quotient geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    {X Q : Over B.base} [IsReduced X.left] [IsLocallyNoetherian X.left]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left}

theorem arithmetic_scalar_parameter_isNoetherian
    (D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding) (φ : B.R →+* D.R) :
    IsNoetherian ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q).left := by
  let Y := (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q
  have : LocallyOfFiniteType Y.hom := inferInstanceAs
    (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd Q.hom (Spec.map (CommRingCat.ofHom φ))))
  have : QuasiCompact Y.hom := inferInstanceAs
    (QuasiCompact (CategoryTheory.Limits.pullback.snd Q.hom (Spec.map (CommRingCat.ofHom φ))))
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  exact ⟨⟩

def arithmetic_reduced_pel_family
    (D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding) (φ : B.R →+* D.R)
    (hφ : D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField)
    (A : U.PrescribedAbelianPair hU π hk (Spec.map (CommRingCat.ofHom φ)))
    (hrigid : U.PrescribedRigid) :
    PEL.Has.IntegralPELObject P (B.compose D).R ((B.compose D).integralEmbedding iota) N
      (Reduction.reduction ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q)) := by
  have := arithmetic_scalar_parameter_isNoetherian B (Q := Q) D φ
  let C := A.reducedPELObject φ hrigid
  exact {
    data := C.data
    rosati := C.rosati
    lieRanks := (B.compose_integralEmbedding D φ hφ iota) ▸ C.lieRanks }

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReducedFamily
