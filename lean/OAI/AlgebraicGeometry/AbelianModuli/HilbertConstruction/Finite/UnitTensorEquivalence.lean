import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Presheaf

/-! # Unit Tensor Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.UnitTensorEquivalence

noncomputable section

/-! The finite tensor product of rank-one free coefficient modules is the coefficient ring, by multiplication. -/

universe u v

variable (R : Type u) [CommRing R] (ι : Type v) [Fintype ι]

def finiteUnitTensorEquiv : PiTensorProduct R (fun _ : ι => R) ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap (PiTensorProduct.lift (MultilinearMap.mkPiAlgebra R ι R))
    ((LinearMap.id : R →ₗ[R] R).smulRight (PiTensorProduct.tprod R (fun _ : ι => (1 : R))))
    (by
      apply LinearMap.ext
      intro r
      simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, LinearMap.id_apply, map_smul,
        PiTensorProduct.lift.tprod, MultilinearMap.mkPiAlgebra_apply, Finset.prod_const_one, smul_eq_mul, mul_one])
    (by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.lift.tprod,
        LinearMap.smulRight_apply, LinearMap.id_apply, MultilinearMap.mkPiAlgebra_apply]
      exact MultilinearMap.congr_fun
        (MultilinearMap.mkPiRing_apply_one_eq_self (PiTensorProduct.tprod R (s := fun _ : ι => R))) x)

theorem finiteUnitTensorEquiv_tprod (x : ι → R) :
    finiteUnitTensorEquiv R ι (PiTensorProduct.tprod R x) = ∏ i, x i :=
  PiTensorProduct.lift.tprod (φ := MultilinearMap.mkPiAlgebra R ι R) x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.UnitTensorEquivalence
