import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualGroupComparison
import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualData

/-! # Dual Data Equality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.DualDataEquality

noncomputable section

/-! Over an algebraically closed field, the Picard-derived dual data equals the supplied geometric dual data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

private theorem data_ext {S : Scheme.{u}} {A : Over S} [GrpObj A] (D E : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)
    (ha : D.abelian = E.abelian) (hg : HEq D.group E.group)
    (hr : HEq D.representable E.representable) (hp : HEq D.poincare E.poincare) : D = E := by
  cases D
  cases E
  cases ha
  cases hg
  cases hr
  cases hp
  rfl

/-- Rigidity identifies the entire normalized dual datum after its group law is derived from Picard tensor product. -/
theorem withPicardGroup_eq {k : Type u} [Field k] [IsAlgClosed k]
    {A : Over (Spec (.of k))} [GrpObj A] (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) : D.withPicardGroup = D := by
  exact data_ext D.withPicardGroup D rfl (heq_of_eq (Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D)) HEq.rfl HEq.rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.DualDataEquality
