import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PartitionBaseMaps
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.HomEquations

/-! # Partition Group Hom -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PartitionGroupHom

noncomputable section

/-! The actual group-homomorphism equations can be checked on the
components of a finite disjoint partition of the base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

namespace FiniteBasePartition
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.HomEquations.GroupHomEquations
variable {S : Scheme.{0}} {I : Type} [Finite I]
    (U : I → Over S) (T : Over S) (j : ∀ i, U i ⟶ T)
    (H : IsColimit (Cofan.mk T.left (fun i => (j i).left)))
    (G : Over S) [GrpObj G]

include H

theorem respectsGroup_of_restrictions (f : T ⨯ G ⟶ G)
    (hf : ∀ i, Group.HomEquations.GroupHomEquations.RespectsGroup G (prod.map (j i) (𝟙 G) ≫ f)) : Group.HomEquations.GroupHomEquations.RespectsGroup G f := by
  constructor
  · apply Over.OverMorphism.ext
    apply Cofan.IsColimit.hom_ext H
    intro i
    change (j i).left ≫ (Group.HomEquations.GroupHomEquations.unitAxis G T ≫ f).left = (j i).left ≫ (1 : T ⟶ G).left
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, ← Group.HomEquations.GroupHomEquations.unitAxis_naturality,
      Category.assoc, (hf i).1, MonObj.comp_one]
  · apply PartitionBaseMaps.FiniteBasePartition.product_hom_ext U T j H (G ⨯ G) G
    intro i
    rw [← Group.HomEquations.GroupHomEquations.multiplied_restrict, ← Group.HomEquations.GroupHomEquations.multiplyImages_restrict]
    exact (hf i).2

theorem glue_respectsGroup (f : ∀ i, U i ⨯ G ⟶ G) (hf : ∀ i, Group.HomEquations.GroupHomEquations.RespectsGroup G (f i)) :
    Group.HomEquations.GroupHomEquations.RespectsGroup G (PartitionBaseMaps.FiniteBasePartition.glue U T j H G G f) := by
  apply respectsGroup_of_restrictions U T j H G
  intro i
  rw [PartitionBaseMaps.FiniteBasePartition.glue_restrict]
  exact hf i

end FiniteBasePartition

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PartitionGroupHom
