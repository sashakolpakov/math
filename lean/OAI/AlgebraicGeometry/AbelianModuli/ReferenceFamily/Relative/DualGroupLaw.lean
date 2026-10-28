import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.GroupRigidity

/-! # Dual Group Law -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.DualGroupLaw

noncomputable section

/-! The specified dual group law equals Picard tensor product over a
locally noetherian base, by the proved group-rigidity theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison.Construction

theorem dualPicardGroup_eq_given_relative
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ}
    {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : HilbertConstruction.Dual.Data.DualAbelianData A) :
    Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D = D.abelian.group :=
  AbelianScheme.IsogenyQuotient.Noetherian.GroupRigidity.Construction.groupStructure_eq_of_origin_over_noetherian_base D.abelian.scheme
    (Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D) D.abelian.group (Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup_commutative D) (Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup_origin D)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.DualGroupLaw
