import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Subgroup Preimage -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubgroupPreimage.Construction

noncomputable section

/-! Pull back an actual finite subgroup along an isogeny as a group
scheme. Its cover geometry and bounded source torsion follow from the original maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A B J : Grp (Over S)} (f : A ⟶ B) (j : J ⟶ B)

abbrev subgroupPreimage : Grp (Over S) := pullback f j
abbrev subgroupPreimageInclusion : subgroupPreimage f j ⟶ A := pullback.fst f j
abbrev subgroupPreimageProjection : subgroupPreimage f j ⟶ J := pullback.snd f j

theorem subgroupPreimage_square :
    (subgroupPreimageInclusion f j).hom.hom ≫ f.hom.hom =
      (subgroupPreimageProjection f j).hom.hom ≫ j.hom.hom :=
  congrArg (fun t : subgroupPreimage f j ⟶ B => t.hom.hom) (pullback.condition (f := f) (g := j))

theorem subgroupPreimage_isPullback :
    IsPullback (subgroupPreimageInclusion f j).hom.hom
      (subgroupPreimageProjection f j).hom.hom f.hom.hom j.hom.hom :=
  (IsPullback.of_hasPullback f j).map (Grp.forget (Over S))

theorem subgroupPreimage_geometricPullback :
    IsPullback (subgroupPreimageInclusion f j).hom.hom.left
      (subgroupPreimageProjection f j).hom.hom.left f.hom.hom.left j.hom.hom.left :=
  (subgroupPreimage_isPullback f j).map (Over.forget S)

instance subgroupPreimageInclusion_mono [Mono j.hom.hom] :
    Mono (subgroupPreimageInclusion f j).hom.hom :=
  PullbackCone.mono_fst_of_is_pullback_of_mono (subgroupPreimage_isPullback f j).isLimit

instance subgroupPreimageInclusion_closed [IsClosedImmersion j.hom.hom.left] :
    IsClosedImmersion (subgroupPreimageInclusion f j).hom.hom.left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (subgroupPreimage_geometricPullback f j).flip inferInstance

theorem subgroupPreimageProjection_cover
    [IsFinite f.hom.hom.left] [Flat f.hom.hom.left] [LocallyOfFinitePresentation f.hom.hom.left]
    [Surjective f.hom.hom.left] :
    IsFinite (subgroupPreimageProjection f j).hom.hom.left ∧
      Flat (subgroupPreimageProjection f j).hom.hom.left ∧
      LocallyOfFinitePresentation (subgroupPreimageProjection f j).hom.hom.left ∧
      Surjective (subgroupPreimageProjection f j).hom.hom.left := by
  have h := subgroupPreimage_geometricPullback f j
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) h inferInstance,
    MorphismProperty.of_isPullback (P := @Flat) h inferInstance,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h inferInstance,
    MorphismProperty.of_isPullback (P := @Surjective) h inferInstance⟩

variable (m n : ℕ) (hj : j.hom.hom ^ m = 1)
  (hf : ∀ (T : Over S) (x : T ⟶ A.X), x ≫ f.hom.hom = 1 → x ^ n = 1)

include hj hf in
theorem subgroupPreimage_killed : (subgroupPreimageInclusion f j).hom.hom ^ (m * n) = 1 := by
  rw [pow_mul]
  apply hf
  rw [MonObj.pow_comp, subgroupPreimage_square, ← MonObj.comp_pow, hj, MonObj.comp_one]

variable [IsCommMonObj A.X]

def subgroupPreimageSourceTorsionMap : (subgroupPreimage f j).X ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme A.X (m * n) :=
  TorsionQuotient.SubgroupFunctor.torsionLift (m * n) (subgroupPreimageInclusion f j).hom.hom
    (subgroupPreimage_killed f j m n hj hf)

omit [IsCommMonObj A.X] in
theorem subgroupPreimageSourceTorsionMap_inclusion :
    subgroupPreimageSourceTorsionMap f j m n hj hf ≫ TorsionQuotient.SubgroupFunctor.torsionι A.X (m * n) =
      (subgroupPreimageInclusion f j).hom.hom := TorsionQuotient.SubgroupFunctor.torsionLift_ι _ _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubgroupPreimage.Construction
