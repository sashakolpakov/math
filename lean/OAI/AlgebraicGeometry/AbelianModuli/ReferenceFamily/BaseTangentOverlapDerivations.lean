import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OverlapDerivationMap
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentAffineLifts

/-! # Base Tangent Overlap Derivations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentOverlapDerivations

noncomputable section

/-! The actual linear lift of a base tangent vector restricts to
an affine overlap and still induces that same base tangent vector in
the overlap coefficient algebra. -/

variable (k R A D C C' : Type) [Field k] [CommRing R] [CommRing A] [CommRing D]
    [CommRing C] [CommRing C']
    [Algebra k R] [Algebra k A] [Algebra k D] [Algebra k C] [Algebra k C']
    [Algebra R k] [Algebra R A] [Algebra R D] [Algebra R C]
    [Algebra A D] [Algebra A C] [Algebra A C'] [Algebra D C']
    [IsScalarTower k R k] [IsScalarTower k R A] [IsScalarTower k R D] [IsScalarTower k R C]
    [IsScalarTower k A D] [IsScalarTower k A C] [IsScalarTower k A C'] [IsScalarTower k D C']
    [IsScalarTower R A D] [IsScalarTower R A C] [IsScalarTower R k C] [IsScalarTower A D C']
    [Algebra.FormallySmooth R A] [Algebra.FormallyEtale A D]

def baseTangentOverlapDerivation (q : C →ₐ[A] C') : Derivation k R k →ₗ[k] Derivation k D C' :=
  (Affine.OverlapDerivationMap.affineOverlapDerivationMap k A D C C' q).comp (BaseTangentAffineLifts.baseTangentAffineDerivation k R A C)

omit [IsScalarTower k R D] in
theorem baseTangentOverlapDerivation_base (q : C →ₐ[A] C') (d : Derivation k R k) (r : R) :
    baseTangentOverlapDerivation k R A D C C' q d (algebraMap R D r) = algebraMap k C' (d r) := by
  change Affine.OverlapDerivationMap.affineOverlapDerivationMap k A D C C' q (BaseTangentAffineLifts.baseTangentAffineDerivation k R A C d)
    (algebraMap R D r) = _
  rw [IsScalarTower.algebraMap_apply R A D r, Affine.OverlapDerivationMap.affineOverlapDerivationMap_algebraMap]
  have h : BaseTangentAffineLifts.baseTangentAffineDerivation k R A C d (algebraMap R A r) = algebraMap k C (d r) :=
    Smooth.CoefficientDerivationSection.smoothCoefficientDerivationSection_algebraMap k R A C
      (Dual.CoefficientLiftNaturality.coefficientDerivationMap k R k C (IsScalarTower.toAlgHom R k C) d) r
  rw [h]
  exact (q.restrictScalars k).commutes (d r)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentOverlapDerivations
