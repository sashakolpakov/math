import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLimit

/-! # Reference Affine Test Coordinates -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceAffineTestCoordinates.Geometric

noncomputable section

/-! Every original affine test over a ring spectrum is isomorphic
over that same base to the spectrum of its actual global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLimit

variable (k : Type) [CommRing k] (U : Over (Spec (.of k))) [IsAffine U.left]

local instance originalAffineGroundAlgebra : Algebra k Γ(U.left, ⊤) :=
  (Spec.preimage (U.left.isoSpec.inv ≫ U.hom)).hom.toAlgebra

def originalAffineTestIso : U ≅ AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k Γ(U.left, ⊤) :=
  Over.isoMk U.left.isoSpec (by
    change U.left.isoSpec.hom ≫
      Spec.map (Spec.preimage (U.left.isoSpec.inv ≫ U.hom)) = U.hom
    simp)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceAffineTestCoordinates.Geometric
