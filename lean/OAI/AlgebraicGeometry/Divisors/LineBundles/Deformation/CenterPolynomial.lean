import OAI.AlgebraicGeometry.Divisors.LineBundles.ZeroIdealDeformation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Maps

/-! # Center Polynomial -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.CenterPolynomial.BundleCycles

noncomputable section

/-! A homomorphism annihilating the center ideal gives the actual map
from the deformation algebra to the polynomial ring over the center.
Its spectrum is the constant family through the graph and its normal zero section. -/

variable {R S : Type} [CommRing R] [CommRing S] (I : Ideal R)
    (f : R →+* S) (hf : I ≤ RingHom.ker f)

def deformationCenterPolynomialMap : Iff.BundleCycles.deformationAlgebra I →+* Polynomial S :=
  (ZeroIdealDeformation.BundleCycles.zeroDeformationEquiv S).symm.toRingHom.comp (Maps.BundleCycles.deformationMap I ⊥ f hf)

theorem deformationCenterPolynomialMap_toLaurent (a : Iff.BundleCycles.deformationAlgebra I) :
    Polynomial.toLaurent (deformationCenterPolynomialMap I f hf a) =
      AddMonoidAlgebra.mapRingHom ℤ f a.val :=
  congrArg Subtype.val ((ZeroIdealDeformation.BundleCycles.zeroDeformationEquiv S).apply_symm_apply (Maps.BundleCycles.deformationMap I ⊥ f hf a))

theorem deformationCenterPolynomialMap_coeff (a : Iff.BundleCycles.deformationAlgebra I) (n : ℕ) :
    (deformationCenterPolynomialMap I f hf a).coeff n = f (a.val.coeff (n : ℤ)) := by
  have h := congrArg (fun z : LaurentPolynomial S => z.coeff (n : ℤ))
    (deformationCenterPolynomialMap_toLaurent I f hf a)
  rw [Iff.BundleCycles.toLaurent_coeff_nat, AddMonoidAlgebra.coeff_mapRingHom] at h
  exact h

theorem deformationCenterPolynomialMap_algebraMap (r : R) :
    deformationCenterPolynomialMap I f hf (algebraMap R (Iff.BundleCycles.deformationAlgebra I) r) =
      Polynomial.C (f r) := by
  change (ZeroIdealDeformation.BundleCycles.zeroDeformationEquiv S).symm
    (Maps.BundleCycles.deformationMap I ⊥ f hf (algebraMap R (Iff.BundleCycles.deformationAlgebra I) r)) = _
  exact (congrArg (ZeroIdealDeformation.BundleCycles.zeroDeformationEquiv S).symm
    (Maps.BundleCycles.deformationMap_algebraMap I ⊥ f hf r)).trans ((ZeroIdealDeformation.BundleCycles.zeroDeformationEquiv S).symm.commutes (f r))

theorem deformationCenterPolynomialMap_parameter :
    deformationCenterPolynomialMap I f hf (Iff.BundleCycles.deformationParameter I) = Polynomial.X := by
  apply (ZeroIdealDeformation.BundleCycles.zeroDeformationEquiv S).injective
  change (ZeroIdealDeformation.BundleCycles.zeroDeformationEquiv S) ((ZeroIdealDeformation.BundleCycles.zeroDeformationEquiv S).symm
    (Maps.BundleCycles.deformationMap I ⊥ f hf (Iff.BundleCycles.deformationParameter I))) = _
  rw [AlgEquiv.apply_symm_apply]
  exact (Maps.BundleCycles.deformationMap_parameter I ⊥ f hf).trans (ZeroIdealDeformation.BundleCycles.zeroDeformationEquiv_X S).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.CenterPolynomial.BundleCycles
