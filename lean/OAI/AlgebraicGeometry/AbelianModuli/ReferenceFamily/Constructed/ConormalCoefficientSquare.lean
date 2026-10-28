import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormalNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SubtypeEquivCongruence

/-! # Conormal Coefficient Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalCoefficientSquare

noncomputable section

/-! Any actual commuting coefficient square of group lifts and their
references induces the same square in the constructed conormal coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (A : Over (Spec (.of k))) [GrpObj A] [Smooth A.hom]
    (C C' : Type) [CommRing C] [CommRing C'] [Algebra k C] [Algebra k C'] (q : C →ₐ[k] C')
    (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A) (c' : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C') ⟶ A)
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c})
    (g : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C') ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C' ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C' ≫ c'})
    (hc : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap q) ≫ c = c')
    (hf : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap q) ≫ f.val = g.val)

include hc hf in
theorem constructedIdentityLiftConormalEquiv_square (z : IdentityConormal.constructedIdentityConormal k A) :
    IdentityConormal.constructedIdentityLiftConormalEquiv k A C' c' g z = q (IdentityConormal.constructedIdentityLiftConormalEquiv k A C c f z) := by
  have he := SubtypeEquivCongruence.subtypeFamilyEquiv_congr
    (fun c' f' : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C') ⟶ A => Dual.CoefficientSchemeTests.dualCoefficientOrigin k C' ≫ f' = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C' ≫ c')
    (IdentityConormal.constructedIdentityLiftConormalEquiv k A C') hc
    (IdentityConormalNaturality.constructedIdentityRestrictedLift k A C C' q c f) g hf
  exact (congrArg (fun l => l z) he).symm.trans
    (IdentityConormalNaturality.constructedIdentityLiftConormalEquiv_natural k A C C' q c f z)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalCoefficientSquare
