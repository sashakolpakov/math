import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Quotient Prime Module -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.QuotientPrimeModule.Constructions

noncomputable section

/-! Under a surjective algebra map, the quotient by a prime and its
inverse-image quotient are the same module over the original ring. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (hs : Function.Surjective (algebraMap R S)) (q : Ideal S)

include hs in
theorem quotient_algebraMap_surjective : Function.Surjective (algebraMap R (S ⧸ q)) := by
  rw [IsScalarTower.algebraMap_eq R S (S ⧸ q)]
  exact Ideal.Quotient.mk_surjective.comp hs

theorem quotient_algebraMap_kernel : RingHom.ker (algebraMap R (S ⧸ q)) = q.comap (algebraMap R S) := by
  ext a
  change algebraMap R (S ⧸ q) a = 0 ↔ algebraMap R S a ∈ q
  rw [IsScalarTower.algebraMap_apply R S (S ⧸ q), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem]

def quotientComapEquiv : (R ⧸ q.comap (algebraMap R S)) ≃ₗ[R] (S ⧸ q) :=
  (Submodule.quotEquivOfEq _ _ (quotient_algebraMap_kernel R S q).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (show Function.Surjective (Algebra.ofId R (S ⧸ q)) from quotient_algebraMap_surjective R S hs q)).toLinearEquiv

theorem quotientComapEquiv_symm_algebraMap_smul (a : R) (b : S ⧸ q) :
    (quotientComapEquiv R S hs q).symm (algebraMap R S a • b) =
      a • (quotientComapEquiv R S hs q).symm b := by
  rw [algebraMap_smul, map_smul]

theorem quotientComapEquiv_algebraMap_smul (a : R) (b : R ⧸ q.comap (algebraMap R S)) :
    (quotientComapEquiv R S hs q) (a • b) =
      algebraMap R S a • (quotientComapEquiv R S hs q) b := by
  rw [algebraMap_smul, map_smul]

def restrictedQuotientIso :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S (S ⧸ q)) ≅
      ModuleCat.of R (R ⧸ q.comap (algebraMap R S)) where
  hom := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S (S ⧸ q)))
    (Y := ModuleCat.of R (R ⧸ q.comap (algebraMap R S)))
    { toFun := (quotientComapEquiv R S hs q).symm
      map_add' := (quotientComapEquiv R S hs q).symm.map_add
      map_smul' := quotientComapEquiv_symm_algebraMap_smul R S hs q }
  inv := ModuleCat.ofHom
    (X := ModuleCat.of R (R ⧸ q.comap (algebraMap R S)))
    (Y := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S (S ⧸ q)))
    { toFun := quotientComapEquiv R S hs q
      map_add' := (quotientComapEquiv R S hs q).map_add
      map_smul' := quotientComapEquiv_algebraMap_smul R S hs q }
  hom_inv_id := ModuleCat.hom_ext (LinearMap.ext (fun b => (quotientComapEquiv R S hs q).apply_symm_apply b))
  inv_hom_id := ModuleCat.hom_ext (LinearMap.ext (fun b => (quotientComapEquiv R S hs q).symm_apply_apply b))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.QuotientPrimeModule.Constructions
