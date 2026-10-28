import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.GradedMap

/-! # Linear Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LinearEquiv.BundleCycles

noncomputable section

/-! A genuine linear isomorphism induces an actual isomorphism
of symmetric algebras, with its literal generator formula. -/

variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)

theorem symmetricGradedMap_linearEquiv_leftInverse :
    Function.LeftInverse (GradedMap.BundleCycles.symmetricGradedMap e.symm.toLinearMap) (GradedMap.BundleCycles.symmetricGradedMap e.toLinearMap) := by
  intro a
  have hc : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    ext m
    exact e.symm_apply_apply m
  have h := GradedMap.BundleCycles.symmetricGradedMap_comp e.toLinearMap e.symm.toLinearMap
  rw [hc, GradedMap.BundleCycles.symmetricGradedMap_id] at h
  exact DFunLike.congr_fun h a

def symmetricLinearEquiv : SymmetricAlgebra R M ≃+* SymmetricAlgebra R N :=
  { (GradedMap.BundleCycles.symmetricGradedMap e.toLinearMap).toRingHom with
    invFun := GradedMap.BundleCycles.symmetricGradedMap e.symm.toLinearMap
    left_inv := symmetricGradedMap_linearEquiv_leftInverse e
    right_inv := symmetricGradedMap_linearEquiv_leftInverse e.symm }

theorem symmetricLinearEquiv_generator (m : M) :
    symmetricLinearEquiv e (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (e m) :=
  GradedMap.BundleCycles.symmetricGradedMap_generator e.toLinearMap m

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LinearEquiv.BundleCycles
