import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.StructurePicardBound
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeComparison
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeEtaleCriterion
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.GeometricPointSurjectivity
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Bound Picard Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.BoundPicardComparison

noncomputable section

/-! A supplied genuine field H1 bound makes the original Picard
comparison etale. Geometric surjectivity realizes each homogeneous
family on every locally Noetherian test, with no characteristic restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeEtaleCriterion.Geometric.RelativeRigidifiedCharts OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

variable {S : Scheme} {g : ℕ}
    (A B : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (hH1 : A.HasFieldStructureH1Bound)
    (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A.scheme B.scheme)
    (hinj : ∀ V : Over S, Function.Injective (D.relativeValue (T := V)))
    {U : Over S} [hU : IsLocallyNoetherian U.left]
    (M : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A.scheme U)

local instance fieldBoundComparison_projection_finiteType :
    LocallyOfFiniteType (snd B.scheme U).left :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd B.scheme.hom U.hom))

local instance fieldBoundComparison_product_noetherian :
    IsLocallyNoetherian (B.scheme ⊗ U).left :=
  LocallyOfFiniteType.isLocallyNoetherian (snd B.scheme U).left

local instance fieldBoundComparison_projection_smoothDimension :
    SmoothOfRelativeDimension g (snd B.scheme U).left :=
  (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback
    (IsPullback.of_hasPullback B.scheme.hom U.hom) B.smoothDimension

include hH1 P hinj hU

theorem fieldBoundPicardComparison_etale :
    Etale (Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparisonProjection P D M).left := by
  let C := Picard.ThetaConstruction.RelativeComparison.Geometric.relativeComparisonLine D M
  let π := Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparisonProjection P D M
  let : Mono π := Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparisonProjection_mono P D M hinj
  let : Mono π.left := Over.mono_left_of_mono π
  let : FormallyUnramified ((Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme C P).hom ≫ (snd B.scheme U).left) :=
    inferInstanceAs (FormallyUnramified π.left)
  apply Picard.ThetaConstruction.RelativeEtaleCriterion.Geometric.RelativeRigidifiedCharts.zeroProjection_etale P C g (snd B.scheme U).left
  intro z
  exact StructurePicardBound.fieldBound_zero_stalk_H1_le_dimension A P hH1 C z

theorem fieldBoundPicardComparison_openImmersion :
    IsOpenImmersion (Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparisonProjection P D M).left := by
  let : Etale (Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparisonProjection P D M).left :=
    fieldBoundPicardComparison_etale A B P hH1 D hinj M
  let : Mono (Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparisonProjection P D M) :=
    Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparisonProjection_mono P D M hinj
  exact IsOpenImmersion.of_flat_of_mono _

variable
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k] (f : Spec (.of k) ⟶ S)
      (x : A.homogeneousPicardSheaf.obj.obj
        (.op ((Over.map f).obj (Over.mk (𝟙 (Spec (.of k))))))),
      ∃ a : (Over.map f).obj (Over.mk (𝟙 (Spec (.of k)))) ⟶ B.scheme,
        D.relativeValue a = A.homogeneousPicardSheafInclusion.hom.app
          (.op ((Over.map f).obj (Over.mk (𝟙 (Spec (.of k)))))) x)
    (hM : A.IsHomogeneousPicardClass U (Line.Bundles.LineBundle.classOf M.bundle))

include hgeom hM

omit hH1 hinj in
theorem fieldBoundPicardComparison_surjective :
    Surjective (Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparisonProjection P D M).left := by
  apply Picard.ThetaConstruction.GeometricPointSurjectivity.Geometric.surjective_of_geometricPoint_lifts
  intro k _ _ t
  let f := t ≫ U.hom
  let W := (Over.map f).obj (Over.mk (𝟙 (Spec (.of k))))
  let j : W ⟶ U := Over.homMk t (Category.id_comp f).symm
  let x := RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A M.bundle hM j
  obtain ⟨a, ha⟩ := hgeom k f x
  have he : D.relativeValue a = M.relativeValue j :=
    ha.trans (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget A M.bundle hM j)
  obtain ⟨z, _, hz⟩ := (Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparison_factorization P D M a j).mp he
  exact ⟨z.left, congrArg Over.Hom.left hz⟩

theorem fieldBoundPicardComparison_isIso :
    IsIso (Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparisonProjection P D M) := by
  let π := Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparisonProjection P D M
  let : IsOpenImmersion π.left := fieldBoundPicardComparison_openImmersion A B P hH1 D hinj M
  let : Surjective π.left := fieldBoundPicardComparison_surjective A B P D M hgeom hM
  let : IsIso π.left := (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨inferInstance, inferInstance⟩
  let : IsIso ((Over.forget S).map π) := inferInstanceAs (IsIso π.left)
  exact isIso_of_reflects_iso π (Over.forget _)

theorem fieldBoundPicard_existsUnique_parameter :
    ∃! a : U ⟶ B.scheme, D.relativeValue a = M.relativeValue (𝟙 U) := by
  let π := Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparisonProjection P D M
  let : IsIso π := fieldBoundPicardComparison_isIso A B P hH1 D hinj M hgeom hM
  let a := inv π ≫ Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparisonParameter P D M
  have ha := Picard.ThetaConstruction.RelativeComparison.Geometric.relativePicardComparison_value P D M (inv π)
  rw [IsIso.inv_hom_id] at ha
  exact ⟨a, ha, fun b hb => hinj U (hb.trans ha.symm)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.BoundPicardComparison
