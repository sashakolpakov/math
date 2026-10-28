import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualGroup

/-! # Canonical Dual Data -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms

noncomputable section

/-! Equip normalized Poincare data with the group law represented by
tensor product. The origin and both normalizations are preserved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A : Over S} [GrpObj A] (D : UnbundledDualData.Construction.UnbundledPicard.DualData A)

def UnbundledDualData.Construction.UnbundledPicard.DualData.withPicardGroup : UnbundledDualData.Construction.UnbundledPicard.DualData A where
  abelian := D.abelian
  group := UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  commutative := UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  proper := D.proper
  smooth := D.smooth
  connected := D.connected
  representable := D.representable
  origin T := by
    let := UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    rw [UnbundledGroup.Construction.UnbundledPicard.trivialHomogeneousPicardClass_eq_one]
    exact (UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv D T).map_one
  poincare := D.poincare
  poincareHomogeneous := D.poincareHomogeneous
  universalClass := D.universalClass
  normalizedAtAbelianZero := D.normalizedAtAbelianZero
  normalizedAtDualZero := by
    have hunit := UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_origin D
    have h := D.normalizedAtDualZero
    simp only [Hom.one_def] at h ⊢
    rw [hunit]
    exact h

theorem UnbundledDualData.Construction.UnbundledPicard.DualData.withPicardGroup_group :
    D.withPicardGroup.group = UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D.withPicardGroup := rfl

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms
