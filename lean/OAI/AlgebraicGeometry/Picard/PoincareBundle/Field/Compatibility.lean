import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.GroupRigidity
import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualData

/-! # Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.Compatibility

noncomputable section

/-! The normalized Picard-derived dual retains the original group over any field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)

/-- Faithful algebraic closure proves the dual group-law comparison over the original field. -/
theorem group_eq : Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D = D.group :=
  GroupRigidity.groupStructure_eq_of_origin D.abelian (Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D) D.group
    (Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D) (Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_origin D)

private theorem data_ext {S : Scheme.{u}} {X : Over S} [GrpObj X] (E F : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData X)
    (ha : E.abelian = F.abelian) (hg : HEq E.group F.group)
    (hr : HEq E.representable F.representable) (hp : HEq E.poincare F.poincare) : E = F := by
  cases E
  cases F
  cases ha
  cases hg
  cases hr
  cases hp
  rfl

/-- Both the Poincare bundle and its representing dual data agree, not merely geometric points. -/
theorem data_eq : D.withPicardGroup = D :=
  data_ext D.withPicardGroup D rfl (heq_of_eq (group_eq D)) HEq.rfl HEq.rfl

/-- An original group map is a map into the canonically normalized dual group. -/
theorem isMonHom (ell : A ⟶ D.abelian) [IsMonHom ell] :
    @IsMonHom (Over (Spec (.of k))) _ _ A D.abelian _ (Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D).toMonObj ell := by
  rw [group_eq D]
  infer_instance

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.Compatibility
