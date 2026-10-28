import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferencePowerValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferencePointBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.HomogeneousLineCohomology
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldLineRealizationReflection
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceParameterTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # Difference Nonrealization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.DifferenceNonrealization

noncomputable section

/-! Failure of an ample difference map to realize a line persists for
every tensor power and every field extension. The resulting homogeneous
point ratios therefore have zero genuine cohomology in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of k))) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (L N : Line.Bundles.LineBundle A.scheme.left)

include P

theorem difference_nonrealization_baseChanged_tensorPower
    (hne : ¬ Picard.ThetaConstruction.DifferenceParameterTransport.Geometric.HasDifferenceParameter A L N)
    {K : Type} [Field K] (c : Spec (.of K) ⟶ Spec (.of k)) (m : ℕ)
    (a : Over.mk (𝟙 (Spec (.of K))) ⟶ (A.pullback c).scheme) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference (A.pullback c)
      ((L.tensorPower m).pullback (pullback.fst A.scheme.hom c))).relativeValue a ≠
      Picard.ThetaConstruction.ReferenceLineValues.Geometric.originalLineValue (A.pullback c)
        (Line.Bundles.LineBundle.classOf (N.pullback (pullback.fst A.scheme.hom c)))
        (Over.mk (𝟙 (Spec (.of K)))) := by
  intro ha
  apply hne
  apply Picard.ThetaConstruction.FieldLineRealizationReflection.Geometric.line_realization_of_field_extension A P L N c
  let p := pullback.fst A.scheme.hom c
  have hp : Line.Bundles.LineBundle.classOf ((L.tensorPower m).pullback p) =
      Line.Bundles.LineBundle.classOf ((L.pullback p).tensorPower m) :=
    Quotient.sound ⟨L.powerBaseChangeIso p m⟩
  have hv := Picard.ThetaConstruction.ReferenceDifferenceFamilyMaps.Geometric.relativeDifference_value_class_congr (A.pullback c)
    ((L.tensorPower m).pullback p) ((L.pullback p).tensorPower m) hp a
  exact ⟨a ^ m, DifferencePowerValues.Theta.Geometric.relativeDifference_tensorPower_represents (A.pullback c)
    (P.baseChange c) (L.pullback p) a m _ (hv.symm.trans ha)⟩

theorem differencePointRatio_baseChanged_cohomology_vanish
    (hN : ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf N))
    (hne : ¬ Picard.ThetaConstruction.DifferenceParameterTransport.Geometric.HasDifferenceParameter A L N)
    {K : Type} [Field K] (c : Spec (.of K) ⟶ Spec (.of k)) (m : ℕ)
    (a : Over.mk (𝟙 (Spec (.of K))) ⟶ (A.pullback c).scheme) (q : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
      (DifferencePointBundles.differencePointRatio (A.pullback c)
        ((L.tensorPower m).pullback (pullback.fst A.scheme.hom c))
        (N.pullback (pullback.fst A.scheme.hom c)) a).sheaf q) := by
  apply HomogeneousLineCohomology.nontrivialHomogeneousLine_cohomology_vanish_overField (A.pullback c) _ (P.baseChange c)
  · exact DifferencePointBundles.differencePointRatio_homogeneous (A.pullback c) (P.baseChange c) _ _ a
      (Picard.ThetaConstruction.FieldHomogeneityBaseChange.Geometric.homogeneousLine_baseChange A N c hN)
  · exact DifferencePointBundles.differencePointRatio_nontrivial (A.pullback c) _ _ a
      (difference_nonrealization_baseChanged_tensorPower A P L N hne c m a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.DifferenceNonrealization
