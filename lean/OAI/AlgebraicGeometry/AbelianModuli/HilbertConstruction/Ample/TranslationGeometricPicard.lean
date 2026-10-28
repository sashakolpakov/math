import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.TranslationPicardInjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharZeroFibers
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.GeometricAmpleDifferenceSurjectivity
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.HomogeneousBaseChangeForgetting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback

/-! # Translation Geometric Picard -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample

noncomputable section

/-! Every geometric homogeneous Picard class is realized by the
actual descended difference line. The field has characteristic zero
because its point lies over the rational base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme} [hS : IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g S} {L : Line.Bundles.LineBundle A.scheme.left}
    {P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme} (Q : TranslationQuotient.AmpleTranslationQuotient A L P)

include hS

theorem TranslationQuotient.AmpleTranslationQuotient.descendedDifference_geometric_surjective
    (qS : S ⟶ Spec (.of ℚ)) (hL : L.IsAmple)
    {k : Type} [Field k] [IsAlgClosed k] (f : Spec (.of k) ⟶ S)
    (x : A.homogeneousPicardSheaf.obj.obj
      (.op ((Over.map f).obj (Over.mk (𝟙 (Spec (.of k))))))) :
    ∃ a : (Over.map f).obj (Over.mk (𝟙 (Spec (.of k)))) ⟶ Q.target.scheme,
      Q.descendedDifference.relativeValue a = A.homogeneousPicardSheafInclusion.hom.app
        (.op ((Over.map f).obj (Over.mk (𝟙 (Spec (.of k)))))) x := by
  let : CharZero k := CharZeroFibers.charZero_of_rational_scheme_map (f ≫ qS)
  let : IsAffineHom f := inferInstance
  let p := pullback.fst A.scheme.hom f
  let : IsAffineHom p := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback A.scheme.hom f).flip (inferInstance : IsAffineHom f)
  let Lf := L.pullback p
  have hLf : Lf.IsAmple := hL.pullback_of_isAffineHom p
  let U := Over.mk (𝟙 (Spec (.of k)))
  let x₀ : (A.pullback f).homogeneousPicardSheaf.obj.obj (.op U) :=
    (A.homogeneousPicardBaseChangeEquiv f U).symm x
  obtain ⟨a, ha⟩ := Picard.ThetaConstruction.GeometricAmpleDifferenceSurjectivity.Geometric.geometric_ampleDifference_surjective (A.pullback f) Lf hLf x₀
  let b := A.baseChangePointsEquiv f U a
  refine ⟨b ≫ Q.isogeny.hom, ?_⟩
  rw [Q.descendedDifference_value_pullback]
  have hbase : Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme f U
      ((Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference (A.pullback f) Lf).relativeValue a) =
        (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue b :=
    Picard.ThetaConstruction.DifferenceBaseChangeValues.Geometric.relativeDifference_value_baseChange A L f U a
  have hforget := Picard.ThetaConstruction.HomogeneousBaseChangeForgetting.Geometric.homogeneousBaseChange_forget_at_algClosed A f (𝟙 (Spec (.of k))) x₀
  exact hbase.symm.trans ((congrArg (Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme f U) ha).trans
    (hforget.symm.trans (congrArg
      (A.homogeneousPicardSheafInclusion.hom.app (.op ((Over.map f).obj U)))
      ((A.homogeneousPicardBaseChangeEquiv f U).apply_symm_apply x))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample
