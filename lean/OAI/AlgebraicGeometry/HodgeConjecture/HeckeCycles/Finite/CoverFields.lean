import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ConstructedCover

/-! # Cover Fields -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CoverFields.CM

noncomputable section

/-! Explicit field comparisons for the constructed finite cover,
including the harmless transport between index equality decisions. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group
variable (I : Type*) [Fintype I] [d : DecidableEq I]

theorem action : (ConstructedCover.CM.finiteCover I).action = BareNe.CM.Group.bareAction := by
  have hd : d = Classical.decEq I := Subsingleton.elim _ _
  cases hd
  rfl

theorem projection_matrix (g : BareNe.CM.Group.BareGroup (I := I)) :
    ((ConstructedCover.CM.finiteCover I).project g).val = (BareNe.CM.Group.bareProjection g).val := by
  have hd : d = Classical.decEq I := Subsingleton.elim _ _
  cases hd
  rfl

theorem negOne : (ConstructedCover.CM.finiteCover I).negOne = BareNe.CM.Group.negOne := by
  have hd : d = Classical.decEq I := Subsingleton.elim _ _
  cases hd
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CoverFields.CM
