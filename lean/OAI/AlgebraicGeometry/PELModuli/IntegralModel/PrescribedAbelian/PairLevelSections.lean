import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.LevelRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientOf
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.BaseChangedKernelPair

/-! # Pair Level Sections -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Each prescribed labelled torsion section descends uniquely to the
actual arithmetic abelian quotient, with its exact covering equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b) (hrigid : U.PrescribedRigid)

include hrigid in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.exists_levelSection (c : Multiplicative (Fin (2 * (3 * s)) → ZMod N)) :
    ∃! z : Over.mk (𝟙 ((Over.pullback b).obj Q).left) ⟶ B.abelian.scheme,
      ((Over.pullback b).map π).left ≫ z.left =
        ((Over.pullback b).map (U.prescribedLevelPoint c)).left ≫ B.abelianCover := by
  let F := Over.pullback b
  have : Flat (F.map π).left := MorphismProperty.of_isPullback (Specialization.base_change_square b π)
    (inferInstanceAs (Flat π.left))
  have : Surjective (F.map π).left := MorphismProperty.of_isPullback (Specialization.base_change_square b π)
    (inferInstanceAs (Surjective π.left))
  have : LocallyOfFinitePresentation (F.map π).left := MorphismProperty.of_isPullback
    (Specialization.base_change_square b π) (inferInstanceAs (LocallyOfFinitePresentation π.left))
  have hz : (F.map (U.prescribedLevelPoint c)).left ≫ (F.map U.prescribedProjection).left = 𝟙 _ := by
    have h := congrArg (fun f => (F.map f).left) (U.prescribedLevelPoint_projection c)
    simpa only [F.map_comp, F.map_id, Over.comp_left, Over.id_left] using h
  have hs := congrArg (fun f => (F.map f).left) (U.prescribedLevelOverlap_source c hU π hk)
  have ht := congrArg (fun f => (F.map f).left) (U.prescribedLevelOverlap_target c hU π hk hrigid)
  simp only [F.map_comp, Over.comp_left] at hs ht
  exact Family.QuotientOf.family_quotient_section_descends (F.map π).left (F.map U.prescribedProjection).left
    B.abelian.scheme B.abelianCover B.abelianCartesian.w.symm _ _
    (BaseChangedKernelPair.over_baseChanged_kernelPair b π _ _ hk) _ _ B.abelianKernelPair.w
    (F.map (U.prescribedLevelPoint c)).left hz (F.map (U.prescribedLevelOverlap c hU π hk)).left hs ht

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.levelSection (c : Multiplicative (Fin (2 * (3 * s)) → ZMod N)) :
    Over.mk (𝟙 ((Over.pullback b).obj Q).left) ⟶ B.abelian.scheme :=
  (B.exists_levelSection hrigid c).exists.choose

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.levelSection_cover (c : Multiplicative (Fin (2 * (3 * s)) → ZMod N)) :
    ((Over.pullback b).map π).left ≫ (B.levelSection hrigid c).left =
      ((Over.pullback b).map (U.prescribedLevelPoint c)).left ≫ B.abelianCover :=
  (B.exists_levelSection hrigid c).exists.choose_spec

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
