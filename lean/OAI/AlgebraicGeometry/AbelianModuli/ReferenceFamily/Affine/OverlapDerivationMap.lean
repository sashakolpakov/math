import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleCoefficientDerivationExtension

/-! # Overlap Derivation Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OverlapDerivationMap

noncomputable section

/-! Restriction from an affine family chart to an etale overlap
changes coefficients and extends derivations linearly. Its values on
the original regular functions are exactly the coefficient restrictions. -/

variable (k A D C C' : Type) [CommRing k] [CommRing A] [CommRing D] [CommRing C] [CommRing C']
    [Algebra k A] [Algebra k D] [Algebra k C] [Algebra k C']
    [Algebra A D] [Algebra A C] [Algebra A C'] [Algebra D C']
    [IsScalarTower k A D] [IsScalarTower k A C] [IsScalarTower k A C']
    [IsScalarTower k D C'] [IsScalarTower A D C'] [Algebra.FormallyEtale A D]

def affineOverlapDerivationMap (q : C →ₐ[A] C') : Derivation k A C →ₗ[k] Derivation k D C' :=
  ((EtaleCoefficientDerivationExtension.etaleCoefficientDerivationExtension k A D C').restrictScalars k).comp
    (Dual.CoefficientLiftNaturality.coefficientDerivationMap k A C C' q)

theorem affineOverlapDerivationMap_algebraMap (q : C →ₐ[A] C') (d : Derivation k A C) (a : A) :
    affineOverlapDerivationMap k A D C C' q d (algebraMap A D a) = q (d a) :=
  EtaleCoefficientDerivationExtension.etaleCoefficientDerivationExtension_algebraMap k A D C'
    (Dual.CoefficientLiftNaturality.coefficientDerivationMap k A C C' q d) a

variable (F C'' : Type) [CommRing F] [CommRing C'']
    [Algebra k F] [Algebra k C''] [Algebra A F] [Algebra D F]
    [Algebra A C''] [Algebra D C''] [Algebra F C'']
    [IsScalarTower k A F] [IsScalarTower k D F] [IsScalarTower k A C'']
    [IsScalarTower k D C''] [IsScalarTower k F C''] [IsScalarTower A D F]
    [IsScalarTower A D C''] [IsScalarTower A F C''] [IsScalarTower D F C'']
    [Algebra.FormallyEtale D F] [Algebra.FormallyEtale A F]

theorem affineOverlapDerivationMap_trans (q : C →ₐ[A] C') (r : C' →ₐ[D] C'') (d : Derivation k A C) :
    affineOverlapDerivationMap k D F C' C'' r (affineOverlapDerivationMap k A D C C' q d) =
      affineOverlapDerivationMap k A F C C'' ((r.restrictScalars A).comp q) d := by
  apply EtaleCoefficientLiftEquivalence.etaleCoefficientDerivation_ext k A F C''
  intro a
  rw [IsScalarTower.algebraMap_apply A D F a, affineOverlapDerivationMap_algebraMap,
    affineOverlapDerivationMap_algebraMap]
  rw [← IsScalarTower.algebraMap_apply A D F a, affineOverlapDerivationMap_algebraMap]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OverlapDerivationMap
