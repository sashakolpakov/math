import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SubtypeEquivCongruence

/-! # Conormal Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalCongruence

noncomputable section

/-! Equal actual group lifts with equal reference maps have equal
constructed conormal coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (k : Type) [Field k] (A : Over (Spec (.of k))) [GrpObj A] [Smooth A.hom]
    (C : Type) [CommRing C] [Algebra k C]
    (c c' : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A)
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c})
    (g : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c'})

theorem constructedIdentityLiftConormalEquiv_congr (hc : c = c') (hf : f.val = g.val) :
    IdentityConormal.constructedIdentityLiftConormalEquiv k A C c f = IdentityConormal.constructedIdentityLiftConormalEquiv k A C c' g :=
  SubtypeEquivCongruence.subtypeFamilyEquiv_congr (fun c f => Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c)
    (IdentityConormal.constructedIdentityLiftConormalEquiv k A C) hc f g hf

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalCongruence
