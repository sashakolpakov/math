import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PolarizationRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientOf

/-! # Pair Polarization Cartesian -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

section

/-! The actual universal polarization morphism descends to the prescribed
arithmetic abelian pair through its effective quotient relation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

variable (hrigid : U.PrescribedRigid)

include hrigid in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.exists_polarizationMap :
    ∃! m : B.abelian.scheme ⟶ B.dual.scheme,
      B.abelianCover ≫ m.left = ((Over.pullback b).map U.prescribedPolarization).left ≫ B.dualCover := by
  let F := Over.pullback b
  have hm : (F.map U.prescribedPolarization).left ≫ (F.map U.prescribedDualProjection).left =
      (F.map U.prescribedProjection).left := by
    have h := congrArg (fun f => (F.map f).left) U.prescribedPolarization_projection
    simpa only [F.map_comp, Over.comp_left] using h
  have hs := congrArg (fun f => (F.map f).left) (U.prescribedPolarizationOverlap_source π)
  have ht := congrArg (fun f => (F.map f).left) (U.prescribedPolarizationOverlap_target hU π hk hrigid)
  simp only [F.map_comp, Over.comp_left] at hs ht
  exact Family.QuotientOf.family_quotient_operation_descends (F.map π).left
    (F.map U.prescribedDualProjection).left (F.map U.prescribedProjection).left
    B.dual.scheme B.abelian.scheme B.dualCover B.abelianCover
    B.dualCartesian.w.symm B.abelianCartesian.w.symm _ _ B.dualKernelPair.w
    _ _ B.abelianKernelPair (F.map U.prescribedPolarization).left hm
    (F.map (U.prescribedPolarizationOverlap π)).left hs ht

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationMap : B.abelian.scheme ⟶ B.dual.scheme :=
  (B.exists_polarizationMap hrigid).exists.choose

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationMap_cover :
    B.abelianCover ≫ (B.polarizationMap hrigid).left =
      ((Over.pullback b).map U.prescribedPolarization).left ≫ B.dualCover :=
  (B.exists_polarizationMap hrigid).exists.choose_spec

end

/-! The descended polarization has the original scalar polarization
as its actual pullback along the dual-family cover. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

variable (hrigid : U.PrescribedRigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationMap_cartesian :
    IsPullback B.abelianCover ((Over.pullback b).map U.prescribedPolarization).left
      (B.polarizationMap hrigid).left B.dualCover := by
  have hm : ((Over.pullback b).map U.prescribedPolarization).left ≫
      ((Over.pullback b).map U.prescribedDualProjection).left =
      ((Over.pullback b).map U.prescribedProjection).left := by
    have h := congrArg (fun f => ((Over.pullback b).map f).left) U.prescribedPolarization_projection
    simpa only [Functor.map_comp, Over.comp_left] using h
  have h : IsPullback B.abelianCover
      (((Over.pullback b).map U.prescribedPolarization).left ≫
        ((Over.pullback b).map U.prescribedDualProjection).left)
      ((B.polarizationMap hrigid).left ≫ B.dual.scheme.hom)
      ((Over.pullback b).map π).left := by
    rw [hm, (B.polarizationMap hrigid).w]
    exact B.abelianCartesian.flip
  exact h.of_bot (B.polarizationMap_cover hrigid) B.dualCartesian.flip

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
