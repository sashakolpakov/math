import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftNaturality

/-! # Coefficient Derivation Map Semilinear -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientDerivationMapSemilinear

noncomputable section

/-! Coefficient change on actual derivations is semilinear for the
specified ring map, in addition to being linear over the original base. -/

variable (k B C C' : Type) [CommRing k] [CommRing B] [CommRing C] [CommRing C']
    [Algebra k B] [Algebra k C] [Algebra k C'] [Algebra B C] [Algebra B C']
    [IsScalarTower k B C] [IsScalarTower k B C'] (q : C →ₐ[B] C')

theorem coefficientDerivationMap_smul (c : C) (d : Derivation k B C) :
    Dual.CoefficientLiftNaturality.coefficientDerivationMap k B C C' q (c • d) = q c • Dual.CoefficientLiftNaturality.coefficientDerivationMap k B C C' q d := by
  apply Derivation.ext
  intro b
  change q (c * d b) = q c * q (d b)
  exact q.map_mul c (d b)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientDerivationMapSemilinear
