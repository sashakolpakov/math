import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstructedConormalDeformedNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalCongruence

/-! # Conormal Deformed Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalDeformedSquare

noncomputable section

/-! Actual commuting squares of references and group lifts under a
deformed coefficient map give the corresponding conormal square, with
the original reduced coefficient map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (A : Over (Spec (.of k))) [GrpObj A] [Smooth A.hom]
    (C D : Type) [CommRing C] [CommRing D] [Algebra k C] [Algebra k D]
    (q : C →ₐ[k] D) (m : DualNumber C →ₐ[k] DualNumber D)
    (hred : ∀ u, (m u).fst = q u.fst) (heps : m DualNumber.eps = DualNumber.eps)
    (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A) (c' : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber D) ⟶ A)
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c})
    (v : {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber D) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k D ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin k D ≫ c'})
    (hc : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m ≫ c = c')
    (hu : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m ≫ u.val = v.val)

include hred heps hc hu

theorem constructedIdentityLiftConormalEquiv_deformed_square (z : IdentityConormal.constructedIdentityConormal k A) :
    IdentityConormal.constructedIdentityLiftConormalEquiv k A D c' v z =
      q (IdentityConormal.constructedIdentityLiftConormalEquiv k A C c u z) := by
  have H := ConormalCongruence.constructedIdentityLiftConormalEquiv_congr k A D
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m ≫ c) c'
    (ConstructedConormalDeformedNaturality.constructedIdentityDeformedLift k A C D q m hred c u) v hc hu
  exact (congrArg (fun w => w z) H).symm.trans
    (ConstructedConormalDeformedNaturality.constructedIdentityLiftConormalEquiv_deformed_natural k A C D q m hred c u heps z)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalDeformedSquare
