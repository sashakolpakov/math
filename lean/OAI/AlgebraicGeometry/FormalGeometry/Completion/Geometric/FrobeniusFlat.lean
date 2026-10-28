import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupHomFlat
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.MapBaseChange

/-! # Frobenius Flat -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.FrobeniusFlat.Construction

noncomputable section

/-! Flatness of the actual geometric Frobenius follows from its group law and finiteness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.Obj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [Fintype k]
  (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [Smooth A.hom]

/-- The literal geometric Frobenius is flat, proved by generic freeness and actual translations. -/
theorem geometricSchemeFrobenius_flat : Flat (Frobenius.Construction.geometricSchemeFrobenius k A) := by
  let B := Frobenius.Construction.geometricFiberOver k A
  let f : B ⟶ B := (Over.pullback (Frobenius.Construction.algebraicClosureBase k)).map (Frobenius.Construction.finiteFieldSchemeFrobenius k A)
  have : Smooth B.hom := inferInstanceAs (Smooth (pullback.snd A.hom (Frobenius.Construction.algebraicClosureBase k)))
  have : IsFinite f.left := MapBaseChange.Construction.geometricSchemeFrobenius_finite k A
  have : Surjective f.left := MapBaseChange.Construction.geometricSchemeFrobenius_surjective k A
  exact Finite.GroupHomFlat.Construction.finite_surjective_groupHom_flat f

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.FrobeniusFlat.Construction
