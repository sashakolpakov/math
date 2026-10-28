import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericIdentities

/-! # Correspondence Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CorrespondenceRestriction.IsogenyQuotient

noncomputable section

/-! Restriction of an actual finite étale correspondence along a moduli
comparison. The source is a scheme-theoretic pullback. Its branch equivalence
preserves individual points and their target images, including repetitions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences

universe u
variable {B : Scheme.{u}} {X Y : Over B}
  (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence Y) (i : X ⟶ Y)

abbrev restrictedCover : Over B := pullback C.source i

abbrev restrictedSource : restrictedCover C i ⟶ X := pullback.snd C.source i

instance restrictedSource_finite : IsFinite (restrictedSource C i).left :=
  MorphismProperty.of_isPullback (P := @IsFinite)
    ((Over.forget B).map_isPullback (IsPullback.of_hasPullback C.source i)) C.finite

instance restrictedSource_etale : Etale (restrictedSource C i).left :=
  MorphismProperty.of_isPullback (P := @Etale)
    ((Over.forget B).map_isPullback (IsPullback.of_hasPullback C.source i)) C.etale

abbrev restrictCorrespondence (target : restrictedCover C i ⟶ X) : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X where
  cover := restrictedCover C i
  source := restrictedSource C i
  target := target
  finite := inferInstance
  etale := inferInstance

variable (target : restrictedCover C i ⟶ X)

def restrictionFiberEquiv {T : Over B} (x : T ⟶ X) :
    (restrictCorrespondence C i target).Fiber x ≃ C.Fiber (x ≫ i) where
  toFun z := ⟨z.val ≫ pullback.fst C.source i, by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun f => f ≫ i) z.property⟩
  invFun z := ⟨pullback.lift z.val x z.property, pullback.lift_snd _ _ _⟩
  left_inv z := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans z.property.symm
  right_inv z := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _

theorem restrictionFiberEquiv_endpoint
    (htarget : target ≫ i = pullback.fst C.source i ≫ C.target)
    {T : Over B} (x : T ⟶ X)
    (z : (restrictCorrespondence C i target).Fiber x) :
    (restrictCorrespondence C i target).endpoint z ≫ i =
      C.endpoint (restrictionFiberEquiv C i target x z) := by
  change (z.val ≫ target) ≫ i = (z.val ≫ pullback.fst C.source i) ≫ C.target
  rw [Category.assoc, htarget, Category.assoc]

theorem restrictedCover_reduced [IsReduced X.left] [IsLocallyNoetherian X.left] :
    IsReduced (restrictedCover C i).left := by
  let : GeometricallyReduced (restrictedSource C i).left :=
    PELModuli.IntegralModel.GenericIdentities.geometricallyReduced_of_smooth (restrictedSource C i).left
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    (restrictedSource C i).left

/-- The only factorization needed for the target is that of its actual
map from the reduced source cover. This follows from reduction's universal
property when the comparison is the retained reduced model map. -/
theorem exists_restricted_target [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hlift : ∀ (T : Over B) [IsReduced T.left],
      Function.Surjective (fun f : T ⟶ X => f ≫ i)) :
    ∃ target : restrictedCover C i ⟶ X,
      target ≫ i = pullback.fst C.source i ≫ C.target := by
  let : IsReduced (restrictedCover C i).left := restrictedCover_reduced C i
  exact hlift (restrictedCover C i) (pullback.fst C.source i ≫ C.target)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CorrespondenceRestriction.IsogenyQuotient
