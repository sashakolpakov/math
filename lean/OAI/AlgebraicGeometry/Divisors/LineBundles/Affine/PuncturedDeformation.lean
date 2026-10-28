import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Specialization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.FiberGenericPoint

/-! # Punctured Deformation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PuncturedDeformation.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the actual Laurent chart of a punctured affine deformation
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R : Type} [CommRing R] (I : Ideal R)

def affinePuncturedDeformationMap : Spec (CommRingCat.of (LaurentPolynomial R)) ⟶ Deformation.ClosedSupport.BundleCycles.affineDeformation I :=
  Spec.map (CommRingCat.ofHom (algebraMap (Deformation.Iff.BundleCycles.deformationAlgebra I) (LaurentPolynomial R)))

instance affinePuncturedDeformationMap_openImmersion : IsOpenImmersion (affinePuncturedDeformationMap I) :=
  IsOpenImmersion.of_isLocalization (Deformation.Iff.BundleCycles.deformationParameter I)

theorem affinePuncturedDeformationMap_range :
    Set.range (affinePuncturedDeformationMap I) =
      ((Deformation.ClosedSupport.BundleCycles.affineDeformation I).basicOpen (Specialization.BundleCycles.affineDeformationParameterSection I) : Set (Deformation.ClosedSupport.BundleCycles.affineDeformation I)) := by
  change Set.range (PrimeSpectrum.comap (algebraMap (Deformation.Iff.BundleCycles.deformationAlgebra I) (LaurentPolynomial R))) = _
  rw [PrimeSpectrum.localization_away_comap_range (LaurentPolynomial R) (Deformation.Iff.BundleCycles.deformationParameter I)]
  exact (congrArg (fun U : (Deformation.ClosedSupport.BundleCycles.affineDeformation I).Opens => (U : Set (Deformation.ClosedSupport.BundleCycles.affineDeformation I)))
    (basicOpen_eq_of_affine (Deformation.Iff.BundleCycles.deformationParameter I))).symm

theorem affinePuncturedDeformationMap_toBase :
    affinePuncturedDeformationMap I ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I))) = Laurent.FiberGenericPoint.BundleCycles.laurentProjection R := by
  exact (Spec.map_comp (CommRingCat.ofHom (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I)))
    (CommRingCat.ofHom (algebraMap (Deformation.Iff.BundleCycles.deformationAlgebra I) (LaurentPolynomial R)))).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PuncturedDeformation.BundleCycles
