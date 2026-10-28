import OAI.AlgebraicGeometry.FormalGeometry.Completion.OpenImmersionOverLift
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Birational.Dominant
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Dominant Open Group Points -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantOpenGroupPoints

noncomputable section

/-! A dense open subgroup contains every rational point: each translate
of its open image meets that image, and division supplies a lift. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  {A B : Over (Spec (CommRingCat.of K))} [GrpObj A] [GrpObj B]
  [LocallyOfFiniteType B.hom]
  (f : A ⟶ B) [IsMonHom f] [IsOpenImmersion f.left] [IsDominant f.left]

theorem dominantOpen_groupHom_point_surjective (b : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B) :
    ∃ a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, a ≫ f = b := by
  have : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
  let β : A ⟶ B := f ≫ (GrpObj.mulRight b).hom
  have : IsOpenImmersion β.left :=
    inferInstanceAs (IsOpenImmersion (f.left ≫ (GrpObj.mulRight b).hom.left))
  have hβ : (Set.range β.left).Nonempty :=
    ⟨β.left ((MonObj.one (X := A)).left (IsLocalRing.closedPoint K)), ⟨_, rfl⟩⟩
  have hnonempty : (Set.range f.left ∩ Set.range β.left).Nonempty := by
    simpa only [Set.inter_comm] using
      f.left.denseRange.inter_open_nonempty _ β.left.isOpenEmbedding.isOpen_range hβ
  obtain ⟨w, hw, hwc⟩ := nonempty_inter_closedPoints hnonempty
    (f.left.isOpenEmbedding.isOpen_range.inter β.left.isOpenEmbedding.isOpen_range).isLocallyClosed
  let p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B :=
    Over.homMk (pointOfClosedPoint B.hom w hwc) (pointOfClosedPoint_comp B.hom w hwc)
  have hp (z : Spec (CommRingCat.of K)) : p.left z = w :=
    pointOfClosedPoint_apply B.hom w hwc z
  obtain ⟨a, ha⟩ := OpenImmersionOverLift.Construction.overOpenImmersion_hasLift f p (by
    rintro _ ⟨z, rfl⟩
    rw [hp]
    exact hw.1)
  obtain ⟨c, hc⟩ := OpenImmersionOverLift.Construction.overOpenImmersion_hasLift β p (by
    rintro _ ⟨z, rfl⟩
    rw [hp]
    exact hw.2)
  have hcb : (c ≫ f) * b = p := by
    change c ≫ (f ≫ (𝟙 B * (toUnit B ≫ b))) = p at hc
    simpa only [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc,
      toUnit_unit, Category.id_comp] using hc
  refine ⟨c⁻¹ * a, ?_⟩
  rw [MonObj.mul_comp, GrpObj.inv_comp, ha, ← hcb]
  exact inv_mul_cancel_left (c ≫ f) b

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantOpenGroupPoints
