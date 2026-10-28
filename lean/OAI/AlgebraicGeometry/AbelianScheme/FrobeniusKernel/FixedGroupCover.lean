import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteFlatCoverRetract
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-! # Fixed Group Cover -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FixedGroupCover.Construction

noncomputable section

/-! An idempotent group endomorphism preserving a cover to J cuts out
a finite flat cover of J by its fixed subgroup. The retraction is over J. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) (e : G ⟶ G) (he : e ≫ e = e)

abbrev fixedGroup : Grp (Over S) := equalizer e (𝟙 G)
abbrev fixedGroupInclusion : fixedGroup G e ⟶ G := equalizer.ι e (𝟙 G)

def fixedGroupRetraction : G ⟶ fixedGroup G e :=
  equalizer.lift e (he.trans (Category.comp_id e).symm)

theorem fixedGroupRetraction_inclusion : fixedGroupRetraction G e he ≫ fixedGroupInclusion G e = e :=
  equalizer.lift_ι _ _

theorem fixedGroupInclusion_retraction :
    fixedGroupInclusion G e ≫ fixedGroupRetraction G e he = 𝟙 (fixedGroup G e) := by
  apply equalizer.hom_ext
  rw [Category.assoc, fixedGroupRetraction_inclusion, Category.id_comp]
  exact (equalizer.condition e (𝟙 G)).trans (Category.comp_id _)

variable {J : Grp (Over S)} (p : G ⟶ J) (hp : e ≫ p = p)

abbrev fixedGroupTargetOver : Over J.X.left :=
  Over.mk ((fixedGroupInclusion G e).hom.hom.left ≫ p.hom.hom.left)

def fixedGroupTargetInclusion : fixedGroupTargetOver G e p ⟶ Over.mk p.hom.hom.left :=
  Over.homMk (fixedGroupInclusion G e).hom.hom.left rfl

def fixedGroupTargetRetraction : Over.mk p.hom.hom.left ⟶ fixedGroupTargetOver G e p :=
  Over.homMk (fixedGroupRetraction G e he).hom.hom.left (by
    change (fixedGroupRetraction G e he).hom.hom.left ≫
      (fixedGroupInclusion G e).hom.hom.left ≫ p.hom.hom.left = p.hom.hom.left
    rw [← Category.assoc]
    have h : (fixedGroupRetraction G e he).hom.hom.left ≫ (fixedGroupInclusion G e).hom.hom.left =
        e.hom.hom.left :=
      congrArg (fun t : G ⟶ G => t.hom.hom.left) (fixedGroupRetraction_inclusion G e he)
    rw [h]
    exact congrArg (fun t : G ⟶ J => t.hom.hom.left) hp)

theorem fixedGroupTarget_retraction :
    fixedGroupTargetInclusion G e p ≫ fixedGroupTargetRetraction G e he p hp =
      𝟙 (fixedGroupTargetOver G e p) := by
  apply Over.OverMorphism.ext
  exact congrArg (fun t : fixedGroup G e ⟶ fixedGroup G e => t.hom.hom.left)
    (fixedGroupInclusion_retraction G e he)

include he hp in
theorem fixedGroupProjection_cover
    [IsFinite p.hom.hom.left] [Flat p.hom.hom.left] [LocallyOfFinitePresentation p.hom.hom.left]
    [Surjective p.hom.hom.left] :
    IsFinite (fixedGroupTargetOver G e p).hom ∧
      Flat (fixedGroupTargetOver G e p).hom ∧
      LocallyOfFinitePresentation (fixedGroupTargetOver G e p).hom ∧
      Surjective (fixedGroupTargetOver G e p).hom := by
  let : IsFinite (Over.mk p.hom.hom.left).hom := inferInstanceAs (IsFinite p.hom.hom.left)
  let : Flat (Over.mk p.hom.hom.left).hom := inferInstanceAs (Flat p.hom.hom.left)
  let : LocallyOfFinitePresentation (Over.mk p.hom.hom.left).hom :=
    inferInstanceAs (LocallyOfFinitePresentation p.hom.hom.left)
  let : Surjective (Over.mk p.hom.hom.left).hom := inferInstanceAs (Surjective p.hom.hom.left)
  exact FiniteFlatCoverRetract.Construction.finite_flat_cover_of_over_retract (fixedGroupTargetInclusion G e p)
    (fixedGroupTargetRetraction G e he p hp) (fixedGroupTarget_retraction G e he p hp)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FixedGroupCover.Construction
