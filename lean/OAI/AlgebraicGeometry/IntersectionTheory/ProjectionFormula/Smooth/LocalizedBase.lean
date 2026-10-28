import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalFiber
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Localized Base -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalizedBase

noncomputable section

/-! Localizing both sides of a smooth algebra gives a local domain
closed fiber. The intermediate smooth presentation is the actual tensor
product with the localized base. -/

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

universe u

theorem quotient_domain (R A T S : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.Smooth R A]
    [CommRing T] [IsLocalRing T] [Algebra R T]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Algebra T S] [Algebra A S]
    [IsScalarTower R T S] [IsScalarTower R A S] [IsLocalHom (algebraMap T S)]
    (N : Submonoid R) (M : Submonoid A) [IsLocalization N T] [IsLocalization M S]
    (hNM : Algebra.algebraMapSubmonoid A N ≤ M) :
    IsDomain (S ⧸ (IsLocalRing.maximalIdeal T).map (algebraMap T S)) := by
  let B := T ⊗[R] A
  let φ : B →ₐ[T] S := Algebra.TensorProduct.lift (Algebra.ofId T S)
    (IsScalarTower.toAlgHom R A S) (fun _ _ => Commute.all _ _)
  let : Algebra B S := φ.toRingHom.toAlgebra
  let : IsScalarTower T B S := IsScalarTower.of_algebraMap_eq' (by
    ext t
    exact (φ.commutes t).symm)
  let : Algebra A B := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap A S a = φ (1 ⊗ₜ[R] a)
    rw [Algebra.TensorProduct.lift_tmul]
    simp only [map_one, one_mul]
    rfl)
  let : IsLocalization (Algebra.algebraMapSubmonoid A N) B := IsLocalization.tensorRight T N
  let : IsLocalization (M.map (algebraMap A B)) S :=
    IsLocalization.isLocalization_of_submonoid_le B S (Algebra.algebraMapSubmonoid A N) M hNM
  exact LocalFiber.quotient_domain T B S (M.map (algebraMap A B))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalizedBase
