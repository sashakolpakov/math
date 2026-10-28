import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedGroupRigidity

/-! # Dual Group Law -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DualGroupLaw

noncomputable section

/-! The specified dual group law equals Picard tensor product over a
reduced locally noetherian base, by the proved group-rigidity theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison.Construction

theorem dualPicardGroup_eq_given_relative
    {S : Scheme.{0}} [IsReduced S] [IsLocallyNoetherian S] {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) :
    Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D = D.abelian.group :=
  AbelianScheme.IsogenyQuotient.ReducedGroupRigidity.Construction.groupStructure_eq_of_origin_over_reduced_base D.abelian.scheme
    (Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D) D.abelian.group (Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup_commutative D) (Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup_origin D)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DualGroupLaw
